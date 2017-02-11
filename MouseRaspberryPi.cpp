#include "opencv2/imgproc/imgproc.hpp"
#include <opencv2/opencv.hpp>
#include "opencv2/highgui/highgui.hpp"
#include <raspicam/raspicam_cv.h>
#include <iostream>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <stropts.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <linux/input.h>
#include <bluetooth/bluetooth.h>
#include <bluetooth/hci.h>
#include <bluetooth/hci_lib.h>
#include <bluetooth/l2cap.h>
#include <bluetooth/sdp.h>
#include <bluetooth/sdp_lib.h>
#include <omp.h>
#include <limits>
#include <cmath>   

using namespace std;
using namespace cv;

#define PSMHIDCTL 0x11
#define PSMHIDINT 0x13
#define SDPRECORDFILE "/etc/bluetooth/hid-sdp-record.bin"
#define HIDINFO_NAME  "Raspberry Pi mouse"
#define HIDINFO_PROV  "HID Mouse simulation via Bluetooth"
#define HIDINFO_DESC  "Raspberry Pi as a mouse"
#define SDPRECORD "\x05\x01\x09\x02\xA1\x01\x85\x01\x09\x01\xA1\x00" \
      "\x05\x09\x19\x01\x29\x03\x15\x00\x25\x01\x75\x01" \
      "\x95\x03\x81\x02\x75\x05\x95\x01\x81\x01\x05\x01" \
      "\x09\x30\x09\x31\x09\x38\x15\x81\x25\x7F\x75\x08" \
      "\x95\x02\x81\x06\xC0\xC0\x05\x01\x09\x06\xA1\x01" \
      "\x85\x02\xA1\x00\x05\x07\x19\xE0\x29\xE7\x15\x00" \
      "\x25\x01\x75\x01\x95\x08\x81\x02\x95\x08\x75\x08" \
      "\x15\x00\x25\x65\x05\x07\x19\x00\x29\x65\x81\x00" \
      "\xC0\xC0"
#define SDPRECORD_BYTES 98

/*-----------------------------------------------------------------------*/
/*Variables globales*/
/*IHM*/
Mat img;
int positionRectangleX, positionRectangleY;
clock_t start = 0, start_menu = 0;
bool inCenterRectangle = false;
bool inMenu = false;
int menu_choisi = 0;

/*Bluetooth*/
unsigned int sdphandle = 0;
int sint,  sctl;
const bdaddr_t tmp = {{0, 0, 0, 0, 0, 0}};
const bdaddr_t tmp2 = {{0, 0, 0, 0xff, 0xff, 0xff}};
double mLastMoveX = numeric_limits<double>::max();
double mLastMoveY = numeric_limits<double>::max();
clock_t startLastClick = 0;
bool maintenuRelache = false;

/*-----------------------------------------------------------------------*/
/*Structures de données*/

struct hidrep_mouse_t
{
  unsigned char btcode; // 0xA1
  unsigned char rep_id; // 0x02
  unsigned char button; // 00000<MBtn><RBtn><LBtn>
  signed   char axis_x; // coordonnées : x
  signed   char axis_y; // coordonnées : y
  signed   char axis_z; // scroll wheel
};

/*-----------------------------------------------------------------------*/
/*Fonctions*/
static void add_lang_attr(sdp_record_t *r); // ajoute l'attribut langue au sdp record.
int dosdpregistration (void); //enregistre le sdp record.
int	btbind (int sockfd,unsigned short port); //relie un socket à un port.
void sendVide(); //envoie une trame HID vide pour maintenur la connection.
void sendMouseEvent(int x, int y); //envoie une trame HID contenant les coordonnées x et y du curseur.
void overlayImage(const Mat &background, const Mat &foreground, Mat &output, Point2i location); //ajoute une image overlay
void CallBackFunc(int x, int y);//fonction appellée à chaque changement de x et y
void sendClickSimple();//envoie un click simple dans une trame HID
void sendClickDouble();//envoie un click double dans une trame HID
void sendClickDroit();//envoie un click droit dans une trame HID
void sendEndClickSimpleMaintenu();//envoie une une trame HID pour annuler le maintenu/relâché
void send_click(int menu);//envoie un click selon le menu choisi
/*-----------------------------------------------------------------------*/



static void add_lang_attr(sdp_record_t *r)
{
    sdp_lang_attr_t base_lang;
    sdp_list_t *langs = 0;
    base_lang.code_ISO639 = (0x65 << 8) | 0x6e;
    base_lang.encoding = 106;
    base_lang.base_offset = SDP_PRIMARY_LANG_BASE;
    langs = sdp_list_append(0, &base_lang);
    sdp_set_lang_attr(r, langs);
    sdp_list_free(langs, 0);
}

int dosdpregistration ( void )
{
	sdp_record_t  record;
	sdp_session_t *session;
    sdp_list_t  *svclass_id,*pfseq,*apseq,*root;
    uuid_t    root_uuid,hidkb_uuid,l2cap_uuid,hidp_uuid;
    sdp_profile_desc_t  profile[1];
    sdp_list_t  *aproto,*proto[3];
    sdp_data_t  *psm,*lang_lst,*lang_lst2,*hid_spec_lst,*hid_spec_lst2;
    void    *dtds[2],*values[2],*dtds2[2],*values2[2];
    int   i,leng[2];
    uint8_t   dtd=SDP_UINT16,dtd2=SDP_UINT8,dtd_data=SDP_TEXT_STR8,hid_spec_type=0x22;
    uint16_t  hid_attr_lang[]={0x409, 0x100},ctrl=PSMHIDCTL,intr=PSMHIDINT,hid_attr[]={0x100, 0x111, 0x40, 0x00, 0x01, 0x01},hid_attr2[]={0x100, 0x0};

	  	// Connect to SDP server on localhost, to publish service information
		session = sdp_connect ( &tmp, &tmp2, 0 );
		if ( ! session )
		{
		    fprintf ( stderr, "Failed to connect to SDP server: %s\n",
		        strerror ( errno ) );
		    return  1;
		}
	    memset(&record, 0, sizeof(sdp_record_t));
	    record.handle = 0xffffffff;
	  	// Make HID service visible (add to PUBLIC BROWSE GROUP)
	    sdp_uuid16_create(&root_uuid, PUBLIC_BROWSE_GROUP);
	    root = sdp_list_append(0, &root_uuid);
	    sdp_set_browse_groups(&record, root);
	  	//Language Information to be added
	    add_lang_attr(&record);
	  	//The descriptor for the keyboard
        sdp_uuid16_create(&hidkb_uuid, HID_SVCLASS_ID);
        svclass_id = sdp_list_append(0, &hidkb_uuid);
        sdp_set_service_classes(&record, svclass_id);
  		// And information about the HID profile used
        sdp_uuid16_create(&profile[0].uuid, HIDP_UUID /*HID_PROFILE_ID*/);
        profile[0].version = 0x0100;
        pfseq = sdp_list_append(0, profile);
        sdp_set_profile_descs(&record, pfseq);
  		// We are using L2CAP, so add an info about that
        sdp_uuid16_create(&l2cap_uuid, L2CAP_UUID);
        proto[1] = sdp_list_append(0, &l2cap_uuid);
        psm = sdp_data_alloc(SDP_UINT16, &ctrl);
        proto[1] = sdp_list_append(proto[1], psm);
        apseq = sdp_list_append(0, proto[1]);
  		// And about our purpose, the HID protocol data transfer
        sdp_uuid16_create(&hidp_uuid, HIDP_UUID);
        proto[2] = sdp_list_append(0, &hidp_uuid);
        apseq = sdp_list_append(apseq, proto[2]);
        aproto = sdp_list_append(0, apseq);
        sdp_set_access_protos(&record, aproto);
        proto[1] = sdp_list_append(0, &l2cap_uuid);
        psm = sdp_data_alloc(SDP_UINT16, &intr);
        proto[1] = sdp_list_append(proto[1], psm);
        apseq = sdp_list_append(0, proto[1]);
        sdp_uuid16_create(&hidp_uuid, HIDP_UUID);
        proto[2] = sdp_list_append(0, &hidp_uuid);
        apseq = sdp_list_append(apseq, proto[2]);
        aproto = sdp_list_append(0, apseq);
        sdp_set_add_access_protos(&record, aproto);
  		// Set service name, description
        sdp_set_info_attr(&record, HIDINFO_NAME, HIDINFO_PROV, HIDINFO_DESC);
  		// Add a few HID-specifid pieces of information
        sdp_attr_add_new(&record, SDP_ATTR_HID_DEVICE_RELEASE_NUMBER,
                                        SDP_UINT16, &hid_attr[0]); 
        sdp_attr_add_new(&record, SDP_ATTR_HID_PARSER_VERSION,
                                        SDP_UINT16, &hid_attr[1]); 
        sdp_attr_add_new(&record, SDP_ATTR_HID_DEVICE_SUBCLASS,
                                        SDP_UINT8, &hid_attr[2]); 
        sdp_attr_add_new(&record, SDP_ATTR_HID_COUNTRY_CODE,
                                        SDP_UINT8, &hid_attr[3]); 
        sdp_attr_add_new(&record, SDP_ATTR_HID_VIRTUAL_CABLE,
                                  SDP_BOOL, &hid_attr[4]); 
        sdp_attr_add_new(&record, SDP_ATTR_HID_RECONNECT_INITIATE,
                                  SDP_BOOL, &hid_attr[5]); 
		// Add the HID descriptor (describing the virtual device) as code
		// SDP_ATTR_HID_DESCRIPTOR_LIST (0x206 IIRC)
        dtds[0] = &dtd2;
        values[0] = &hid_spec_type;
        dtd_data= SDPRECORD_BYTES <= 255 ? SDP_TEXT_STR8 : SDP_TEXT_STR16 ;
        dtds[1] = &dtd_data;
        values[1] = (uint8_t *) SDPRECORD;
        leng[0] = 0;
        leng[1] = SDPRECORD_BYTES;
        hid_spec_lst = sdp_seq_alloc_with_length(dtds, values, leng, 2);
        hid_spec_lst2 = sdp_data_alloc(SDP_SEQ8, hid_spec_lst);
        sdp_attr_add(&record, SDP_ATTR_HID_DESCRIPTOR_LIST, hid_spec_lst2);
  		// and continue adding further data bytes for 0x206+x values
        for (i = 0; i < sizeof(hid_attr_lang) / 2; i++) {
                dtds2[i] = &dtd;
                values2[i] = &hid_attr_lang[i];
        }
        lang_lst = sdp_seq_alloc(dtds2, values2, sizeof(hid_attr_lang) / 2);
        lang_lst2 = sdp_data_alloc(SDP_SEQ8, lang_lst);
        sdp_attr_add(&record, SDP_ATTR_HID_LANG_ID_BASE_LIST, lang_lst2);
  		sdp_attr_add_new ( &record, SDP_ATTR_HID_PROFILE_VERSION,SDP_UINT16, &hid_attr2[0] );
  		sdp_attr_add_new ( &record, SDP_ATTR_HID_BOOT_DEVICE,SDP_UINT16, &hid_attr2[1] );
  		// Submit SDP record to the "sdpd"
        if (sdp_record_register(session, &record, SDP_RECORD_PERSIST) < 0) {
                fprintf ( stderr, "Service Record registration failed\n" );
                return -1;
        }
		// Store the service handle retrieved from there for reference (i.e.,
		// deleting the service info when this program terminates)
		sdphandle = record.handle;
		fprintf ( stdout, "HID keyboard/mouse service registered\n" );
		        
		return 0;
}

int	btbind ( int sockfd, unsigned short port ) {
	struct sockaddr_l2 l2a;
	int i;
	memset ( &l2a, 0, sizeof(l2a) );
	l2a.l2_family = AF_BLUETOOTH;
	bacpy ( &l2a.l2_bdaddr, &tmp );
	l2a.l2_psm = htobs ( port );
	i = bind ( sockfd, (struct sockaddr *)&l2a, sizeof(l2a) );
	if ( 0 > i )
	{
		fprintf ( stderr, "Bind error (PSM %d): %s\n",
				port, strerror ( errno ) );
	}
	return	i;
}

void sendVide()
{
	char    hidrep[32];
	hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0x0;
    hid_mouse->rep_id = 0x0;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0x0;
    hid_mouse->axis_y = 0x0;

	send (sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL);
}


void sendMouseEvent(int x, int y)
{
	int distanceX = 0, distanceY = 0;
	char  hidrep[32];
	unsigned char but;

	if(maintenuRelache)
	    but = 0x01;
	else
	    but = 0x0;

	hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
	hid_mouse->btcode = 0xA1;
	hid_mouse->rep_id = 0x01;
	hid_mouse->button = but;
	hid_mouse->axis_x = x;
	hid_mouse->axis_y = y;
	hid_mouse->axis_z = 0;
  
    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
}

void overlayImage(const Mat &background, const Mat &foreground, Mat &output, Point2i location)
{
  background.copyTo(output);
  for(int y = max(location.y , 0); y < background.rows; ++y)
  {
    int fY = y - location.y; 
    if(fY >= foreground.rows)
      break;

    for(int x = max(location.x, 0); x < background.cols; ++x)
    {
      int fX = x - location.x; 

      if(fX >= foreground.cols)
        break;

      double opacity =
        ((double)foreground.data[fY * foreground.step + fX * foreground.channels() + 3])

        / 255.;

      for(int c = 0; opacity > 0 && c < output.channels(); ++c)
      {
        unsigned char foregroundPx =
          foreground.data[fY * foreground.step + fX * foreground.channels() + c];
        unsigned char backgroundPx =
          background.data[y * background.step + x * background.channels() + c];
        output.data[y*output.step + output.channels()*x + c] =
          backgroundPx * (1.-opacity) + foregroundPx * opacity;
      }
    }
  }
}

void CallBackFunc(int x, int y)
{ 
       if(!inMenu)
        {
		  start_menu = 0;
                    //rect 1
                  if(x<=160 && y<=106)
                  {
                    positionRectangleX = 0;positionRectangleY = 0;
                    inCenterRectangle = false;
		    		sendMouseEvent(-10, -10);
                  }

                  //rect 2
                  if(x<=320 && x>160 && y<=106)
                  {
                    positionRectangleX = 160;positionRectangleY = 0;
                    inCenterRectangle = false;
                    sendMouseEvent(0, -10);
                  }

                  //rect 3
                  if(x>320 && y<=106)
                  {
                    positionRectangleX = 320;positionRectangleY = 0;
                    inCenterRectangle = false;
		    		sendMouseEvent(10, -10);
                  }

                  //rect 4
                  if(x<=160 && y>106 && y<=212)
                  {
                    positionRectangleX = 0;positionRectangleY = 106;
                    inCenterRectangle = false;
		    		sendMouseEvent(-10, 0);
                  }

                  //rect 5
                  if(x<=320 && x>160 && y<=212 && y>106)
                  {
                    positionRectangleX = 160;positionRectangleY = 106;
            		    if(!inCenterRectangle)                  
            			     start = clock();
            		    inCenterRectangle = true;
                  }

                  //rect 6
                  if(x>320 && y<=212 && y>106)
                  {
                    positionRectangleX = 320;positionRectangleY = 106;
                    inCenterRectangle = false;
		    		sendMouseEvent(10, 0);
                  }

                  //rect 7
                  if(x<=160 && y>160 && y>212)
                  {
                    positionRectangleX = 0;positionRectangleY = 212;
                    inCenterRectangle = false;
		    	    sendMouseEvent(-10, 10);
                  }

                  //rect 8
                  if(x<=320 && x>160 && y>212)
                  {
                    positionRectangleX = 160;positionRectangleY = 212;
                    inCenterRectangle = false;
		    		sendMouseEvent(0, 10);
                  }

                  //rect 9
                  if(x>320 && y>212)
                  {
                    positionRectangleX = 320;positionRectangleY = 212;
                    inCenterRectangle = false;
		    		sendMouseEvent(10, 10);
		
                  }

        }else{
                  //click simple
                  if(x>=0 && x<=90)
                  {
	              	  if(menu_choisi!=1)		    
	              		start = clock();
	                  menu_choisi = 1;
                  }

                  //click double
                  if(x>90 && x<=186)
                  {
	                    if(menu_choisi!=2)		    
				          start = clock();
	                    menu_choisi = 2;
                  }

                  //click droit
                  if(x>186 && x<=275)
                  {
	                    if(menu_choisi!=3)		    
				            start = clock();
	                    menu_choisi = 3;
                  }

                  //M/R
                  if(x>275 && x<=373)
                  {
	                    if(menu_choisi!=4)		    
				            start = clock();
	                    menu_choisi = 4;
                  }

                  //Annuler
                  if(x>373)
                  {
	                    if(menu_choisi!=5)		    
				            start = clock();
	                    menu_choisi = 5;
                  }


        }
          
          

     
}


void sendClickSimple()
{
    char    hidrep[32];
    hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x01;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );

    hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
}

void sendClickDouble()
{
    char    hidrep[32];
    hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x01;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );

    hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );

    hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );

    hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;

    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );

}

void sendClickDroit()
{
    char    hidrep[32];
    hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x02;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;
    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
    hid_mouse = (hidrep_mouse_t *)hidrep;
    hid_mouse->btcode = 0xA1;
    hid_mouse->rep_id = 0x01;
    hid_mouse->button = 0x0;
    hid_mouse->axis_x = 0;
    hid_mouse->axis_y = 0;
    hid_mouse->axis_z = 0;
    send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
}

void sendClickSimpleMaintenu()
{
  char    hidrep[32];
  hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
  hid_mouse->btcode = 0xA1;
  hid_mouse->rep_id = 0x01;
  hid_mouse->button = 0x01;
  hid_mouse->axis_x = 0;
  hid_mouse->axis_y = 0;
  hid_mouse->axis_z = 0;
  send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
}

void sendEndClickSimpleMaintenu()
{
  char    hidrep[32];
  hidrep_mouse_t* hid_mouse = (hidrep_mouse_t *)hidrep;
  hid_mouse->btcode = 0xA1;
  hid_mouse->rep_id = 0x01;
  hid_mouse->button = 0x0;
  hid_mouse->axis_x = 0;
  hid_mouse->axis_y = 0;
  hid_mouse->axis_z = 0;
  send ( sint, hid_mouse, sizeof(struct hidrep_mouse_t), MSG_NOSIGNAL );
}

void send_click(int menu)
{
    switch(menu)
    {
      case 1 : sendClickSimple();break;
      case 2 : sendClickDouble();break;
      case 3 : sendClickDroit();break;
      case 4 : 
      {
                                            if(!maintenuRelache)
                                            {
                                              maintenuRelache = true;
                                            }
                                            else
                                            {
                                              sendEndClickSimpleMaintenu();
                                              maintenuRelache = false;
                                            }
      }break;
    }
} 

int main(int argc, char** argv)
{

    /*Bluetooth*/
    int sockint, sockctl;
    struct sockaddr_l2  l2a;
    socklen_t alen;

    /*Raspberry Pi reconnue en tant que SOURIS*/
    system("hciconfig hci0 class 0x002580");
    system("hciconfig hci0 name Raspberry");
    system("hciconfig hci0 piscan");
    
    /*Enregistrement du SDP Record*/
    cout << "Registering SDP ...\n";
         if ( dosdpregistration() < 0)
    {
      fprintf(stderr,"Failed to register with SDP server\n");
      return  -1;
    }
    cout << "SDP registered ...\n";

    /*SOCKETS*/
    alen=sizeof(l2a);
    sockint = socket ( AF_BLUETOOTH, SOCK_SEQPACKET, BTPROTO_L2CAP );
    sockctl = socket ( AF_BLUETOOTH, SOCK_SEQPACKET, BTPROTO_L2CAP );
    if ( ( 0 > sockint ) || ( 0 > sockctl ) )
    {
      fprintf ( stderr, "Failed to generate bluetooth sockets\n" );
      return  -1;
    }

    /*Lier les sockets aux ports*/
    cout << "Binding sockets ...\n";
    if ( btbind ( sockint, PSMHIDINT ) || btbind ( sockctl, PSMHIDCTL ))
    {
      fprintf ( stderr, "Failed to bind sockets (%d/%d) "
          "to PSM (%d/%d)\n",
          sockctl, sockint, PSMHIDCTL, PSMHIDINT );
      return  -1;
    }
      cout << "Sockets bound ...\n";

    /*Attendre qu'un périphérique se connecte*/
    cout << "Listening ...\n";
    if ( listen ( sockint, 1 ) || listen ( sockctl, 1 ) )
    {
      fprintf ( stderr, "Failed to listen on int/ctl BT socket\n" );
      close ( sockint );
      close ( sockctl );
      return  -1;
    }

    /*Accepter la connection*/
    cout << "Accepting ...";
    sctl = accept ( sockctl, (struct sockaddr *)&l2a, &alen );
    sint = accept ( sockint, (struct sockaddr *)&l2a, &alen );

    cout << "Got a connection on the control channel" << sctl << "\n";
    cout << "Got a connection on the interrupt channel" << sint << "\n";
  
    int k;  double duration = 0.0, duration_menu = 0.0; 
    string menu_choisi_str = "Click simple";
    string menu_tab[] = {"Click simple","Click double","Click droit","Maintenu/relache"};
    raspicam::RaspiCam_Cv cap;
    cap.set(CV_CAP_PROP_FORMAT, CV_8UC3);
    cap.set(CV_CAP_PROP_FRAME_WIDTH, 480);
    cap.set(CV_CAP_PROP_FRAME_HEIGHT, 320);
    namedWindow("mousePI", WINDOW_NORMAL);
    resizeWindow("mousePI", 480,320);
    cvSetWindowProperty("mousePI", CV_WND_PROP_FULLSCREEN, CV_WINDOW_FULLSCREEN);
    Mat foreground = imread("overlay2.png", -1);
    resize(foreground,foreground,Size(480,320));
    Mat menu = imread("menuClicks.png", -1);
    resize(menu,menu,Size(480,320));
    Mat rectangle = imread("rectangle_rouge.png", -1);
    resize(rectangle,rectangle,Size(160,106));

    int pos_x=-1;
    int pos_y=-1;
    Mat imgCalibre;
    Mat imgHSV;
    Mat imgFinale;
    double dureeLastMove = 0.0;
    startLastClick  = clock();
    if (!cap.open())
	  {
		std::cerr <<"Cannot open the camera" << endl;
	  }

    while(cap.isOpened())
    {
    	//envoyer une trame vide chaque seconde pour maintenir la connexion Bluetooth
		dureeLastMove = (clock() - startLastClick) / (double) CLOCKS_PER_SEC;
		if(dureeLastMove >= 1) 
	        	sendVide();
        //Tracking
	    Mat image;
	    cap.grab();
	    cap.retrieve(image);
		
    	cvtColor(image, imgHSV, COLOR_BGR2HSV);

    		
    	inRange(imgHSV, Scalar(170, 0, 0), Scalar(179,255,255), imgCalibre);
    		
    	Moments oMoments = moments(imgCalibre);

    	double dM01 = oMoments.m01;
    	double dM10 = oMoments.m10;
    	double dSurface = oMoments.m00;
   
    	imgCalibre = Mat::zeros(imgCalibre.size(), CV_8UC3);
    	
    	//recuperation des coordonnées
	    if(dSurface > 1000) 
	    {
	    			pos_x=dM10/dSurface;
	    			pos_y=dM01/dSurface;
	    }
    		
        if(pos_x >= 0 && pos_y >=0) 
        {
    			line(imgCalibre, Point(pos_x-10,pos_y), Point(pos_x+10, pos_y), Scalar(255,0,255), 2);
    			line(imgCalibre, Point(pos_x,pos_y-10), Point(pos_x, pos_y+10), Scalar(255,0,255), 2);
    			cout << pos_x << endl;
    			cout << pos_y << endl;
    	
    			cout << "    " << endl;
    	}

    	img = imgCalibre;
    	//fonction de callback 
      	CallBackFunc(pos_x, pos_y);
      	//superposer l'image du rectangle rouge au flux caméra selon les coordonnées de l'objet
      	overlayImage(img,rectangle,img,cv::Point(positionRectangleX,positionRectangleY));
            
      	duration = (clock() - start) /  (double) CLOCKS_PER_SEC;
      		//si le menu est affiché et que le curseur est resté dans la même zone pour au moins 2s --> sortir du menu et envoyer le click
            if(inMenu)
            {
                duration = (clock() - start) / (double) CLOCKS_PER_SEC;
                if(duration >= 2)
                {
                  inMenu = false;
                  inCenterRectangle = false;
                  if(menu_choisi!=5 && menu_choisi!=0)
                    menu_choisi_str = menu_tab[menu_choisi-1];

                  duration_menu = 0.0;
                  send_click(menu_choisi);
                }
            }
            
            //si le curseur est resté dans la zone centrale pour au moins 1s --> afficher le menu
            if(!inMenu)
            {
              
              if(inCenterRectangle && duration >= 1)
              {
                inMenu = true;
                inCenterRectangle = false;
                duration = 0.0;
              }
            }
            

            
            //superposer l'image de la grille au flux caméra
            if(!inMenu)
              overlayImage(img, foreground, img, cv::Point(0,0));
            else
            {
            	//superposer l'image du menu au flux caméra et dessiner le curseur en noir
                overlayImage(img,menu,img,Point(0,0));
    	        line(imgCalibre, Point(pos_x-10,pos_y), Point(pos_x+10, pos_y), Scalar(0,0,0), 2);
    	        line(imgCalibre, Point(pos_x,pos_y-10), Point(pos_x, pos_y+10), Scalar(0,0,0), 2);
            }

            //écrire le menu choisi sur le flux caméra
            putText(img, "Menu choisi : " + menu_choisi_str, cvPoint(10,20), FONT_HERSHEY_TRIPLEX, 0.6, cvScalar(255,255,255), 1, 2.0);
            imshow("mousePI", img);
            k = waitKey(10);
            if (k == 27)
            {
              destroyAllWindows();
              break;
            }
    }
   
    return 0;

}


