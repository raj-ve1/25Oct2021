/* 
 * 
 *    version 17/jul/2020 - direct file fetch instead of JSON to avoid memory frag issues on hexis
 *    version 18/aug/2020 - working with rev 1.0 new board of hexis
 *    version 27/aug/2020 - birthday version :) dirctory sign, improper title fixed up1
 *    version 03/sep/2020 - disable wifi after download, auto download feature
 *    version 21/nov/2020 - configurable student ID. 
 *    version 1/dec/2020 - fixed bug of empty directory, add new folder, new command to move content from new
 *    version 08/feb/2021 - moved to Arduinojson 6 library, made delay from 14msec to 19msec in fire() to fix issues in cells
 *    version 12/feb/2021 - basic MCQ is working
 *    version 17/apr/2021 - many experiments in fire(), not complete; auto scroll speeds added; removed printnextfile and printprevfile; latest file shows up in directory when opened
 *    version 1/may/2021 - lots of finetuning of fire() routine, now rejection is reduced to 15%
 *    version 6/jun/2021 - fixed a crazy bug of lastread pointer; added /etc/lastread to fix it
 *    version 24/aug/2021  - N2,N4 processing changed not to loop
 *    version 29/sept/2021 - wrap word support
 *    version 11/oct/2021 - menu structure changed
 *    version 25/oct/2021 - lots of bug fixes, SD failure fix hopefully
 *    version 11/nov/2021 - delete file after thatv undefined curr/root bug fixed
 *    
 *    (C) All rights reserved, by Vembi Technologies Private Limited
  */
  
#include <Arduino.h>
#include <AsyncEventSource.h>
#include <AsyncJson.h>
#include <AsyncWebSocket.h>
#include <ESPAsyncWebServer.h>
#include <AsyncWebSynchronization.h>
#include <ESPAsyncWebServer.h>
#include <WebAuthentication.h>
#include <WebHandlerImpl.h>
#include <WebResponseImpl.h>
#include <SPI.h>

#include <SD.h>
#include <FS.h>
#include <ArduinoSort.h>

#include <ArduinoJson.h>
//#include "CTBot.h"

#include <WiFi.h>
#include <HTTPClient.h>

#include "esp32-hal-cpu.h"

#define versionDetails "v1.0.3, dated 11th Nov 2021"

/* 
 *  TODO: these buffer sizes are arbitratily defined. need  clarity on them
 */
StaticJsonDocument<10000> jsonBuffer;
StaticJsonDocument<5000> statsBuffer;
StaticJsonDocument<2000> mcqBuffer;
StaticJsonDocument<2000> cfgBuffer;
StaticJsonDocument<3000> lastReadBuffer;

#define CIDARRAYSIZE 200
int cidArray[CIDARRAYSIZE];        // TODO: limit on number of files in a directory
int cidIndex = 0;
int totalCids = 0;

File root;
File curr;
File onfnext;
File saved;

int ret;
int  key;
int dirCursor = 0;
int totalfirings = 0;
int ff00firings = 0;
int onehourff00firings = 0;
int fileposition = 0;


const char *ssid;
const char *password;
const char *servername;


//Not used now.. telegram based remote debugging.. String token = "937005974:AAFr8Ooi4WMkU68az0c3qqma8A-bqEmsid4"    ; // REPLACE myToken WITH YOUR TELEGRAM BOT TOKEN
//#define CHAT_ID 571039562

int hexisId = 0;

#define ONEHOURFIRING 360     // reading rate of 10 sec per line = 6 lines per min = 360 lines per hour
  
#define STACKSIZE 20           // level of nesting of directories allowed. arbitrary value for now TODO
#define LONG_PRESS_TIME 1000    // time in msec to detect long press in msec
File stack[STACKSIZE];        // size of nesting of folders allowed. arbitrary value now. TODO
File popped;
File next;
File cfg;


bool fileopen = false;      // set if user has opened a file in SDcard filesystem
bool mcqAnswerOn = false;
bool autonextline = false;  // autoscroll flag
bool autonextlinemode = false;
bool wordwrap = false;
bool hyphenOn = false;
bool uploadLogFlag = false;
int autonextlineCounter = 0;
int mcqAnswer = 0xff;
bool waitforakey = false;
bool waitforakeymcq = false;
bool testSeqFlag = false;
bool fileDeleted = true;
int testPatternPtr = 0;
bool leafdir = false;
bool sdFailed = false;



#define SLOW 1          
#define MED 2
#define FAST 3
int autonextlinespeed = 0;

#define SLOW_COUNTER 25       // original value for 240Mhz : 50   
#define MED_COUNTER 18       // 40
#define FAST_COUNTER 12       // 30

bool contractMode = false;
bool MCQstart = false;

#define DEBUG_INFO_SIZE 500
char debugInfo[DEBUG_INFO_SIZE];

int debugInfoPtr = 0;
unsigned long onCtr = 0;

HTTPClient http;     
 
int top = -1;

#define CHAR_LEN 20
#define SD_RETRY_COUNT 5          // number of times SD retry before giving up

// Defines for buttons. the digital lines being used by
// the buttons

#define N1 35
#define N2 34
#define N3 32     // originally 33, changed to 32 to fix issue with system #1
#define N4 33    // originally 32, changed to 33 to fix issue with system #1

// These are defines used by cell logic.

// interchange STROBE1 and STROBE2, DATA1 and DATA2 to change from clockwise to anticlockwise and viceversa
//

#define OE1 22 
#define DATA2 17          // original: 17
#define STROBE2 21        // original 21


#define OE2 16 
#define DATA1 15          // original 15
#define STROBE1 4        // original 4
#define CLOCK 2
#define SDCLK 5

#define BUZZER 12  
#define BATTERY 13

// Defines for SDcard


#define KEYPADINTERRUPT 27          // 27 for pre 31/oct/2021 boards and 36 for after that
const byte interruptPin = KEYPADINTERRUPT;      // used for keypad interrupt


uint8_t ch = 0xff; // current value of cell pattern
uint8_t tempdisprev[20];
uint8_t tempdisprevInverted[20];
char temp[20];
uint8_t divider = 3;            // clock divider; allowed values 1, 2,4,8.. 1= default clock speed

/* 
 *  debug definitions
 */
#define NO_DBG_FLAG 0x30       // debug off
#define SD_DBG_FLAG 0x31       // SDCard
#define KP_DBG_FLAG 0x32       // keypad
#define FS_DBG_FLAG 0x35       // FS operations
#define CE_DBG_FLAG 0x36       // cell firing related
#define LS_DBG_FLAG 0x37        // last open file related
#define FULL_DBG_FLAG 0x37     // all

uint8_t debugflag = FS_DBG_FLAG;       

#define DP(a, b) { if ((debugflag == b) || (debugflag == FULL_DBG_FLAG)) {Serial.print(a);} }

int count =0;

const int keypins[] = {N1,N2,N3,N4};

const PROGMEM uint8_t welcome[] = {0x74,0x90,0xa8,0xc0,0x98,0xc8,0x90};

uint8_t dumArray[CHAR_LEN] = {};
int inp[20] = {};

#define  FULLSTOP_BRAILLE 0x34
#define  COMMA_BRAILLE 0x20
#define  SEMICOLON_BRAILLE 0x28
/*
 * Keypad related variables
 */
volatile bool keypressed = false;
volatile int pressedkey = 0;
volatile int kp = 0;
volatile unsigned long ts, nts;
volatile unsigned long starttime, endtime;

volatile unsigned long runningCounter = 0;
volatile bool highon = false;
bool ff00 = false;
bool onehourff00 = false;
unsigned char language = 'e';

struct fib_t {
  int ctype;
  int clang;
  int cls;
  int cid;
  char  title[20];
} ;


/*
 * TODO: These buffer sizes are defined arbitratily :(
 * TODO: can we combine all these buffers to a single large size? at a time only one json decode will be happening? to check
 */
#define STATSARRAYSIZE 5000
char statsbuf[STATSARRAYSIZE];

#define MCQARRAYSIZE 500
char mcqbuf[MCQARRAYSIZE];

#define CFGARRAYSIZE 500
char cfgbuf[CFGARRAYSIZE];

#define LASTREADARRAYSIZE 2000
char lastreadbuf[LASTREADARRAYSIZE];


const char * ctitle;
int ctype;
int clang;
int cid;
int currentCid;
int currentCtype;
unsigned long currentLastRead;
int cca;
const char * cfolder = NULL;
char currentTitle[20];

bool wifi = false;

// braille code lookup table - only to display file name (title) and directory names.
// it is uncontracted only

const   char   chars[] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 
                          'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
                          'w', 'x', 'y', 'z', 
                          0x27, ':', ',', '.',  '!', '-', '?', ';', ' '
                          };

const    uint8_t   hexes[] = {0x80, 0xa0, 0xc0, 0xd0, 0x90, 0xe0, 0xf0, 0xb0, 0x60, 0x70, 0x88,
                              0xa8, 0xc8, 0xd8, 0x98, 0xe8, 0xf8, 0xb8, 0x68, 0x78, 0x8c, 0xac,
                              0x74, 0xcc, 0xdc, 0x9c, 
                              0x80, 0x30, 0x20, 0x34, 0xe0, 0x0c, 0x1c, 0x28, 0x0
                              };
const char testSeq[] = {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 
                          'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
                          'w', 'x', 'y', 'z', 
                          'l', 'x', 'q','a', 'x','g', 'u','x', 's','t','w','r','c','-', 'k', 'l', '-','g','x', '.', ':', 'c', 'a', '.' };
                          
int menuLevel = 0;
/*
 * Command table definitions
 */
#define NO_OF_SETUP_CMDS 9
const char *setupCmds[NO_OF_SETUP_CMDS];
int cmdIndex = 0;
bool cmdMode = true;        // hexis always starts in command mode

#define NO_OF_TOP_LEVEL_CMDS 4
const char *cmds[NO_OF_TOP_LEVEL_CMDS];

#define NO_OF_CHECKHEXIS_CMDS 3
const char *checkHexisCmds[NO_OF_CHECKHEXIS_CMDS];

#define NO_OF_CONNECT_CMDS 2
const char *connectCmds[NO_OF_CHECKHEXIS_CMDS];

#define MAX_ATTEMPTS 6

const char okay[] = "press any key";
const char low[] = "low battery";
const char normal[] = "battery okay";
const char downloading[] = "please wait..";
const char uploading[] = "uploading ans";
const char uploaded[] = "uploaded answers";
const char checking[] = "checking conn";
const char connokay[] = "connection ok";
const char done[] = "new books";
const char nonew[] = "no new books";
const char connfailed[] = "conn failed";
const char downloaderror[] = "download error";
const char starting[] = "starting";

const char sdFailMsg[] = "sd failure";

int contentCount = 0;

#define ALWAYS_ON_CTR 5000      // 15min approx
bool alwaysON = false;
int alwaysOnCtr = 0;

const char helpString[] = "welcome to hexis, a braille book reader for children. You can read class text books, interesting stories and tidbits and more!"
                       " Hexis power key is on left side back. Hexis can be charged with USB on right side. Hexis has four keys, two on left and two on right. You can press right bottom key to see next line or next file."
                       " Bottom left key is to see previous line or previous file. Right top key is to select current file."
                       " Top left key is to close current file or folder."
                       " When you start Hexis, you see books followed by menu. All stories, text books are in books folder. Press top right key to select books."
                       " You will now see folders like stories, textbooks inside books. The first braille cell is all one means that it is a folder which has files."
                       " Click select key (top right) to open stories. You will see first file with first braille cell all down. This means that it is a file which you can open and read."
                       " Click select key to open file. Now you can use left or right keys to read the story."
                       " To summarize, select books, followed by selecting stories or textbooks and selecting the file to read."
                       " When you are done with reading, press close key (top left)."
                       " Hexis allows downloading of new stories and text books. New content is periodically uploaded for children of all classes."
                       " To download new stories and textbooks, select menu, followed by download."
                       " If there is any new book, it will say new books, otherwise it will say no new books."
                       " If the message is conn failure, it is error in downloading new content. Please talk to teacher or parent."
                       " New content is downloaded and stored in stories and textbook folders. Select content followed by stories to see new stories."
                       " Hexis supports ueb contraction. To enable it select menu, contract on."
                       " Hexis supports next line without pressing next line after 10 seconds. To enable it select menu, autoscroll on."
                       " Hexis can check if new content is there every 15 minutes and download automatically. To enable it, select menu, always conn on."
                       " Beware, It may consume more battery power, so use it sparingly."
                       " You can delete all stories by selecting menu, del all files. Use this if you want to clean stories you have read."
                       " Delete menu does not delete textbooks. This is the quick introduction to Hexis. We hope you like Hexis with its ease of use and good content.";


//CTBot myBot;
//TBMessage msg;
//int prevMessageID = 0;

 int fptr = 1;
 int noEntries = 0;
 uint8_t prev[20];              
uint8_t parsedLines[1000][14];
int curLine = 0;


/*
 * Called once at beginning.
 */
void setup()
{
  int count = 0;
  int i;
  String t;
 

   setCpuFrequencyMhz(80); 
    
   Serial.begin(115200);
   debugLogln("Hello");
   debugLog("Speed of CPU is"); debugLogln((String) getCpuFrequencyMhz());
   
    pinMode(interruptPin, INPUT);
    attachInterrupt(digitalPinToInterrupt(interruptPin), intHandler, CHANGE);      
    debugLog("Using ");debugLog(String(SDCLK)); debugLogln(" as SDcard");


 /* 
   *  cell specific setups...
   */

    pinMode(OE1, OUTPUT);
    pinMode(OE2, OUTPUT);
    pinMode(DATA1, OUTPUT);
    pinMode(DATA2, OUTPUT);
    pinMode(STROBE1 , OUTPUT);
    pinMode(STROBE2 , OUTPUT);
    pinMode(CLOCK , OUTPUT);
    digitalWrite(OE1, HIGH);
    digitalWrite(OE2, HIGH);
    digitalWrite(DATA1, LOW);
    digitalWrite(DATA2, LOW);
    digitalWrite(STROBE1 , HIGH);
    digitalWrite(STROBE2 , HIGH);
    digitalWrite(CLOCK , LOW);
  
 //   pinMode(BATTERY, INPUT);  // set pull-up on analog pin 0  

// initializations for buttons
//

    pinMode(BUZZER, OUTPUT); // buzzer change to D3 later TODO
    pinMode(SDCLK, OUTPUT);
    resetints();
    pinMode(N1, INPUT);
    pinMode(N2, INPUT);
    pinMode(N3, INPUT);
    pinMode(N4, INPUT);

    printLine(starting);
    
 ret = SD.begin(5);
  while (ret == false) {
    count++;
   if (count == SD_RETRY_COUNT) {
    dispSDError();
    beep(100);
    delay(500);
    beep(100);
    break;
   }
   ret = SD.begin(5);
   debugLogln((F("SD F")));
   delay(500*divider);
   }
   
   if (sdFailed) {
      debugLogln(F("SD card failed, stopping"));
      return;
   }
 debugLogln((F("SD init done")));       // TODO: to handle failure of SD init.
// openRoot("/nc");
 
  /*
   * print welcome
   */
    for (i=0; i!=14; i++) {
        inp[i] = 0x0;
        dumArray[i] = 0x0;
    }
    
    if (ff00) {
      for (i=0; i!=14; i++) {
        inp[i]=0x0;
      }
    }

  /*
   * Initialize command structures
   */

   cmds[0] = "books";
   cmds[1] = "connect";
   cmds[2] = "setup";
   cmds[3] = "diagnostics";

   setupCmds[0] = "delete stories";
   setupCmds[1] = "change wifipw";
   setupCmds[2] = "autonext slow";
   setupCmds[3] = "autonext fast";
   setupCmds[4] = "autonext off";
   setupCmds[5] = "contract on";
   setupCmds[6] = "contract off";
   setupCmds[7] = "word wrap on";
   setupCmds[8] = "word wrap off";

   connectCmds[0] = "download";
   connectCmds[1] = "upload answers";
   
   checkHexisCmds[0] = "check conn";
   checkHexisCmds[1] = "battery";
   checkHexisCmds[2] = "factory reset";
   
    /* 
     *  load configuration now..
     */

    cfg = SD.open("/etc/cfg", FILE_READ);
    if (!cfg) {
      dispSDError();
      return;
    }
    cfg.read((uint8_t *) &cfgbuf[0], CFGARRAYSIZE);
    DeserializationError error= deserializeJson(cfgBuffer, &cfgbuf[0]);
    if (error) {
              debugLogln(F("/etc/cfg deserializeJson() in init failed with code "));
              debugLogln(error.c_str());
              // dont know what to do now, have to stop as if it is a SD card error
              dispSDError();
              return;
    }
    autonextlinemode = cfgBuffer["autoscroll"];
    autonextlinespeed = cfgBuffer["autonextlinespeed"];
    contractMode = cfgBuffer["contract"];
    alwaysON = cfgBuffer["alwayson"];
    hexisId = cfgBuffer["hexisId"];
    ssid = cfgBuffer["wifiap"];
    password = cfgBuffer["wifipw"];
    servername = cfgBuffer["servername"];
    wordwrap = cfgBuffer["wordwrap"];
    debugLog("ssid:");debugLogln(ssid);
    debugLog("password:");debugLogln(password);
    debugLog("servername:");debugLogln(servername);
    cfg.close();

 
     
    if (contractMode) {
      openRoot("/cc");
    } else {
      openRoot("/nc");
    }
      /* 
     *  Now printe first command
     */
    menuLevel = 0;
    Serial.println(cmds[0]);
    displayCmd(0);
    beep(1000);
    
    /*
     * start now..
     */
    cmdMode = true;
    debugLog("Start heap size:"); debugLogln(String(ESP.getFreeHeap()));
    debugLog("Hexis ID:"); debugLogln((String) hexisId);
    debugLogln(versionDetails);
    
}

void dispSDError()
{
  int i;
   const char *a;
    // inform user and stop.
      i = 0;
      a = &sdFailMsg[0];
      while (*a != 0) {
        inp[i] = convtocode(*a);
        i++;
        a++;
    }
    displine();
    sdFailed = true;
}

void debugLog(String a)
{
  int i;

    

  if ((a.length() + debugInfoPtr) > DEBUG_INFO_SIZE) {

    // transfer to server
    if (uploadLogFlag) {
      uploadLog();
    } 
    for (i = 0; i != DEBUG_INFO_SIZE; i++) {
        debugInfo[i] = 0;
    }
    debugInfoPtr = 0;
  }
  
  for (i = 0; i != a.length(); i++) {
    debugInfo[debugInfoPtr+i] = a[i];
  }
  debugInfoPtr += a.length();
  Serial.print(a);
}

void uploadLog()
{
int attempts = 0;

  http.end();
  
  if (!wifi) {
      WiFi.begin(ssid, password);
      while (WiFi.status() != WL_CONNECTED) {
        attempts++;
        if (attempts == MAX_ATTEMPTS) {
          return;
        }
        delay(1000*divider);
        debugLogln("Uploadlog: Connecting to WiFi..");
      }
    wifi = true;
    debugLogln("Connected to the WiFi network");
  }  
  
  if ((WiFi.status() == WL_CONNECTED)) { //Check the current connection status
      Serial.print("after wificonnect: entry heap size:"); Serial.println(ESP.getFreeHeap());
   
    //    String url = "http://vembi.in/hexis/at/uploadlog.php";
          String url = String(servername) + "uploadlog.php";
          
        http.begin(url.c_str());
         // Specify content-type header
        http.addHeader("Content-Type", "application/x-www-form-urlencoded");
      // Data to send with HTTP POST
        String Data = "id=";
       Data.concat(hexisId);
       Data.concat("&debuginfo=");
      Data.concat(debugInfo);   
      Data.concat("&heap=");
      Data.concat(ESP.getFreeHeap());
              
      // Send HTTP POST request
     int httpResponseCode = http.POST(Data);
        
        Serial.print("httpResponsecode=");
        Serial.println(httpResponseCode);
    }
}

void debugLogln(String a)
{
  int i;
  a += "\n";
  
  if ((a.length() + debugInfoPtr) > DEBUG_INFO_SIZE) {
    debugInfoPtr = 0;
  }
  for (i = 0; i != a.length(); i++) {
    debugInfo[debugInfoPtr+i] = a[i];
  }
  debugInfoPtr += a.length();
  Serial.print(a);
}

void displayHelp()
{
 //close(curr);
   curr.close();
  curr = SD.open("/nc/stories/help");
  Serial.print("SD opened - ");
  fileopen = true;
  nextline();
  
}

void displayHelpold()
{

  int i = 0;
  char *a = (char *) helpString;

    while (*a != 0) {
      inp[i] = convtocode(*a);
      i++;
      a++;
      if (i == 14) {
         if (inp[13] != 0x0) {  // space
           if (inp[12] == 0x0) {
             a -=2;
             inp[12] = 0x0;
             inp[13] = 0x0;
          } else {
            inp[13] = 0xc;   // braille code for hyphen
            a -=1;
          }
      }
      displine();
      delay(9000*divider);
      i = 0;
      }
    }  
}


void displayCmd(int index)
{
    const char *a;
    int i;

    switch (menuLevel) {
      case 0:   // top level menu
        a = cmds[index];
        break;
      case 1:
        a = connectCmds[index];
        break;
      case 2:
        a = setupCmds[index];
        break;
      case 3:
        a = checkHexisCmds[index];
    }
    
    i = 0;
    while (*a != 0) {
      inp[i] = convtocode(*a);
      i++;
      a++;
    }
    displine();
}

void openRoot(char *path)
{

  root.close();
  curr.close();
  //close(root);
  //close(curr);
  root = SD.open(path, FILE_READ);        // change 2409
  if (!root) {
   dispSDError();
    return;
  }
  debugLog("SD opened - "); debugLogln(path);
  curr = root.openNextFile();
 // curr = printNextFile(root);
 printdir((char *) curr.name(), curr.isDirectory());        // XXX
 debugLogln("curr got");
  count = 0;

    
}

void reloadCurrRoot()
{
  char  *cpath = "/cc";
  char  *ncpath = "/nc";
  char *path;

    curr.close();
    root.close();
   
  
  if (contractMode) {
     path = cpath;
    } else {
     path = ncpath;
    }
 
  root = SD.open(path, FILE_READ);        // change 2409
  if (!root) {
   dispSDError();
    return;
  }
  debugLog("SD opened - "); debugLogln(path);
  curr = root.openNextFile();
 // curr = printNextFile(root);
 //printdir((char *) curr.name(), curr.isDirectory());        // XXX
 debugLogln("curr got");
  count = 0;
}

/*
 * Interrupt handler for keypad. handles debounce, identification of key pressed etc
 * Finicky code, touch at your risk :)
 */
void intHandler ()
{
  int i;

   alwaysOnCtr = 0;   // reset the alwaysonctr irrespective if it is on or off.
   
  
  Serial.print("I");
 // for (i = 0; i !=4; i++) {
 //   Serial.print((int) digitalRead(keypins[i]));
 // }
  Serial.print(" ");
  if (digitalRead(KEYPADINTERRUPT) == HIGH) {
     highon = true;
     for (i = 0; i != 4; i++){
      if (whichkey(i)) {
          kp = i;
         break;       
      }
    }
   debugLog("i:");
   debugLog(String(kp));
    
    // to add code if more than one key pressed
    ts = millis();
    return;
  } else {
    if (!highon) {
      return;
    }
    highon = false;

     // if autonextline is on, reset the autonextlinecounter

   if (autonextline) {
    autonextlineCounter = 0;
   }


   if (kp == 0) {
          nts = millis();
          if ((nts - ts) > LONG_PRESS_TIME) {
            pressedkey = 5;
          } else {
            pressedkey = 1;
          }
           keypressed = true;
           ts = 0;
           nts = 0;
           resetints();
           return;
    } 
    if (kp == 1) {
          nts = millis();
          if ((nts - ts) > LONG_PRESS_TIME) {
            pressedkey = 6;
          } else {
            pressedkey = 2;
          }
           keypressed = true;
           ts = 0;
           nts = 0;
           resetints();
           return;
    }
    if (kp == 2) {
            nts = millis();
          if ((nts - ts) > LONG_PRESS_TIME) {
            pressedkey = 7;
          } else {
            pressedkey = 3;
          }
           keypressed = true;
           ts = 0;
           nts = 0;
           resetints();
           return;
    }

    if (kp == 3) {   
       nts = millis();
          if ((nts - ts) > LONG_PRESS_TIME) {
            pressedkey = 8;
          } else {
            pressedkey = 4;
          }
           keypressed = true;
           ts = 0;
           nts = 0;
            resetints();
           return;
    }
  }
}

bool whichkey(int index) {
  if (digitalRead(keypins[index])) {
    return true;
  } else {
    return false;
}
}

void resetints() {
  int i;
  volatile int port;

  for (i = 0; i != 4; i++){
      port = keypins[i];
      pinMode(port, OUTPUT);
      digitalWrite(port, 0);
      }

   pinMode(N1, INPUT);
   pinMode(N2, INPUT);
   pinMode(N3, INPUT);
   pinMode(N4, INPUT);

}

/*
 * Main control code which gets called in a loop
 */
void loop()
{
    int i;

  
  
  /*
   * if SD init has failed, just come out.. cant do anything
   */
  if (sdFailed) {
    return;
  }

  if (testSeqFlag) {
    if (testPatternPtr == sizeof(testSeq)) {
      testPatternPtr = 0;
    }
    for (i=0; i!=14; i++) {
      inp[i] = convtocode(testSeq[testPatternPtr]);
  }
    displine();
    testPatternPtr++;
    delay(5000);
    return;
  }
    
  if (cmdMode) {
    if (alwaysON) {
      alwaysOnCtr++;
      Serial.print("!");
      if (alwaysOnCtr == ALWAYS_ON_CTR) {
         printLine(downloading);
         if (fetchContent()) {
            if (contentCount == 0) {
            printLine(nonew);
          } else {
            printLine(done);
          }
        }
        alwaysOnCtr = 0;
        return;
      }
    }
  }

  if (ff00) {
    if (inp[0] == 0x0) {
      for (i=0; i!=14; i++) {
        inp[i] = 0xff;
      }
    } else {
      for (i=0; i!= 14; i++) {
        inp[i] = 0x00;
      }
    }
    
    dispy();
    ff00firings++;
    Serial.println((ff00firings));
    delay(200*divider);
    return;
  }

   if (onehourff00) {
    for (i=0; i!=14; i++) {
      inp[i] = ~inp[i];
    }
    dispy();
    onehourff00firings++;
    if (onehourff00firings == ONEHOURFIRING) {
      onehourff00 = false;
    }
    Serial.println((onehourff00firings));
    delay(200*divider);
    return;
  }

  
  if (keypressed) {
    keypressed = false;
    debugLog("K:");
    debugLog(String(pressedkey));
    debugLog(" ");
    DP(pressedkey, KP_DBG_FLAG);



    
    switch(pressedkey) {
    case 1:
      handleN1();
      break;
    case 4: 
      handleN4();
      break;
    case 2:
      handleN2();
      break;
    case 3:
      handleN3();
      break;
    case 5:
      handleN5();
      break;
    case 6:
      handleN6();
      break;
    case 7:
      handleN7();
      break;
    case 8:
      handleN8();
      break;
    default:
      Serial.print("Pressed key:"); Serial.println(pressedkey);
  }    
    pressedkey = 0;
  }

  processCmd();         // console commands
  if (!(ff00) && !(onehourff00)) {
      runningCounter++;
      if (runningCounter == 0x50000) {
      Serial.print(F("SL"));
        runningCounter = 0x0;

      }   
  }

  if (fileopen) {
    if (autonextline) {
      Serial.print("!");
      autonextlineCounter++;
      if (autonextlineCounter == SLOW_COUNTER && autonextlinespeed == SLOW) {
        Serial.print("#");
        handleN4();
        autonextlineCounter = 0;
      }
      if (autonextlineCounter == MED_COUNTER && autonextlinespeed == MED) {
        Serial.print("#");
        handleN4();
        autonextlineCounter = 0;
      }
      if (autonextlineCounter == FAST_COUNTER && autonextlinespeed == FAST) {
        Serial.print("#");
        handleN4();
        autonextlineCounter = 0;
      }
          }   
      }

      delay(200*divider);
       onCtr++;
}


// function that connects to WiFi and pulls new content.
// it also uploads the results of the tests and usage stats
// called when pull button is pressed.

bool fetchContent()
{
  
     String nc = "";  
    String cc = "";
    int attempts = 0;
   
    debugLog("fetchcontent:");
    Serial.print("fetchcontent entry heap size:"); Serial.println(ESP.getFreeHeap());
// code for fetching content from server
  WiFi.mode(WIFI_MODE_APSTA);
  
  if (!wifi) {
      WiFi.begin(ssid, password);
      while (WiFi.status() != WL_CONNECTED) {
        attempts++;
        if (attempts == MAX_ATTEMPTS) {
          printLine(connfailed);
          waitforakey = true;
          return false;
        }
        delay(1000*divider);
        debugLogln("FC: Connecting to WiFi..");
      }
    wifi = true;
    debugLogln("Connected to the WiFi network");
  }  
  
 
   
   if ((WiFi.status() == WL_CONNECTED)) { //Check the current connection status
      Serial.print("after wificonnect: entry heap size:"); Serial.println(ESP.getFreeHeap());
       contentCount = 0;
       // get stats and test answers

        fetchStats();
        fetchTestResults();
      //  String url = "http://vembi.in/hexis/at/fetchhexis.php?id=";
        String url = String(servername) + "fetchhexis.php?id=";
        url.concat(hexisId);
        url.concat("&stats=");
        url.concat(&statsbuf[0]);
        url.concat("&mcqans=");
        url.concat(&mcqbuf[0]);

        /* 
         *  added version of firmware as a parameter
         */
         url.concat("&fwver=");
         url.concat(versionDetails);

         
        
         */
        debugLog("url is:"); debugLogln(url);
        http.begin(url); //Specify the URL
       int httpCode = http.GET();                                        //Make the request       
      if (httpCode > 0) { //Check for the returning code
        String payload = http.getString();
 //       Serial.println(httpCode);
          payload.trim();    
          Serial.println(payload);
    //      jsonBuffer.clear();
          deserializeJson(jsonBuffer, payload);
          auto error = deserializeJson(jsonBuffer, payload);
          if (error) {
              debugLog(F("Fetch content deserializeJson() failed with code "));
              debugLogln(error.c_str());
              wifi = false;
              printLine(downloaderror);
              waitforakey = true;
              return false;
          }
 //         JsonArray& myArray = jsonBuffer.parseArray(payload);
          // Test if parsing succeeds.
 //        if (!myArray.success()) {
 //           Serial.println("parseObject() failed");
 //           wifi = false;
 //           return false;
 //        }
          // print contents now
            http.end(); //Free the resources 
             JsonArray v = jsonBuffer.as<JsonArray>();
            for(JsonVariant c : v) {
              Serial.print(".");
              contentCount++;
              JsonObject d = c.as<JsonObject>();
              parseMsg(d);
              downloadFile();
          }
          } else {
          debugLogln("Error on HTTP request");
          printLine(downloaderror);
          return false;
        }
        Serial.print("after downloads: entry heap size:"); Serial.println(ESP.getFreeHeap());
        // disable WiFi to save power TODO
        wifi = false;
        WiFi.mode(WIFI_OFF);
        Serial.print("after disable wifi: entry heap size:"); Serial.println(ESP.getFreeHeap());
        return true;
   } 

   
   
}


void parseMsg(JsonObject& c)
{
      
      debugLog("parseMsg:");
       ctype = c["ctype"];
      clang = c["clang"];
      cid = c["cid"];
      ctitle = c["title"];
      cfolder = c["folder"];
      cca = c["correct_ans"];        // makes sense only for MCQ
           
      Serial.print("cid:");Serial.println(cid);
      Serial.print("ctype:"); Serial.println(ctype);
      Serial.print("clang:"); Serial.println(clang);
      Serial.print("title:"); Serial.println(ctitle); 
      Serial.print("ca:"); Serial.println(cca);
      Serial.print("cfolder:"); Serial.println(cfolder);
}

void getMCQ(JsonObject& c)
{
   const char *q;
   const char *a1;
   const char *a2;
   const char *a3;
   const char *a4;
   const char *ca;
   const char *ac;
   String op;
 
  
   

    
         ac = c["actual_content"];
         Serial.println(ac);
         Serial.print("Contents of MCQ:");
         auto error = deserializeJson(mcqBuffer, ac);
          if (error) {
              Serial.print(F("getMCQ deserializeJson() failed with code "));
              Serial.println(error.c_str());
              wifi = false;
          }
         
         q = mcqBuffer["question"];
         a1 = mcqBuffer["a1"];
         a2 = mcqBuffer["a2"];
         a3 = mcqBuffer["a3"];
         a4 = mcqBuffer["a4"];
         ca = mcqBuffer["ca"];
         
       Serial.print("q:"); Serial.print(q); Serial.print("a1:"); Serial.print( a1); Serial.print("a3:"); Serial.print(a2); Serial.print("a3:"); Serial.print(a3); Serial.print("a4:"); Serial.print(a4); 
       Serial.print("ca:"); Serial.println(ca);

    // now print it on braille
    // first create string to be printed
    
        op = "Question:";
        op.concat(q);
        op.concat("Press 1:");
        op.concat(a1);
        op.concat("2:");
        op.concat(a2);
        op.concat("3:");
        op.concat(a3);
        op.concat("4:");
        op.concat(a4);
        op.concat("Press 3 when ready");
        Serial.println(op);

        // write to file
        
}
void fetchTestResults()
{
  int i;
  char buf[5] = "[]";
   
  
  File mcqf  = SD.open("/etc/mcqans", FILE_READ);
  if (!mcqf) {
        debugLog(F("fetchTestResults Open error of /etc/mcqans"));
        beep(2000);
        // cant do much now..
        return;
    }
    for (i=0; i!= MCQARRAYSIZE; i++) {
      mcqbuf[i] = 0;  
  }
  mcqf.read((uint8_t *) &mcqbuf[0], MCQARRAYSIZE);     
  mcqf.close();
  
  // now make the stats file as null file

  mcqf = SD.open("/etc/mcqans", FILE_WRITE);
  mcqf.write((uint8_t *) buf, 2);
  mcqf.close();
  
}

void fetchStats() 

{
  int i;
  char buf[5] = "[]";
   
  
  File stats  = SD.open("/etc/stats", FILE_READ);
  if (!stats) {
        debugLog(F("fetchStats Open error of /etc/stats"));
        beep(2000);
        // cant do much now..
        return;
    }
    for (i=0; i!= STATSARRAYSIZE; i++) {
      statsbuf[i] = 0;  
  }
  stats.read((uint8_t *) &statsbuf[0], STATSARRAYSIZE);     
  stats.close();
  
  // now make the stats file as null file

  stats = SD.open("/etc/stats", FILE_WRITE);
  stats.write((uint8_t *) buf, 2);
  stats.close();
  
}


void addStats(int cid, int readingtime) 
{
    int i;
    String dest;
    File wstats;
  File stats  = SD.open("/etc/stats", FILE_READ);
  if (!stats) {
        debugLog(F("addStats Open error of /etc/stats"));
        beep(2000);
        // cant do much now..
        return;
    }
    for (i=0; i!= STATSARRAYSIZE; i++) {
      statsbuf[i] = 0;  
  }
  stats.read((uint8_t *) &statsbuf[0], STATSARRAYSIZE);     

 DeserializationError error= deserializeJson(statsBuffer, &statsbuf[0]);
   if (error) {
              debugLog(F("addStats deserializeJson() failed with code "));
              debugLogln(error.c_str());
              wifi = false;
    }
    Serial.print("Contents of stats:");
         JsonArray v = jsonBuffer.as<JsonArray>();
            for(JsonVariant c : v) {
 
       Serial.print("cid:"); Serial.print((int)  c["cid"], DEC); Serial.print("readingtime:"); Serial.print((int) c["readingtime"], DEC); 
       Serial.print(" ");
     }




JsonObject newentry = statsBuffer.createNestedObject();
newentry["cid"] = cid;
newentry["readingtime"] = readingtime;
serializeJson(statsBuffer, Serial);
serializeJson(statsBuffer, dest);
     Serial.print("dest is:"); Serial.println( dest.c_str());
     Serial.print("After printo:"); Serial.print((int)dest.length());
     stats.close();
     
     wstats = SD.open("/etc/stats", FILE_WRITE);
     wstats.write((uint8_t *) dest.c_str(), dest.length());
     
     wstats.close();

     
}

void addMCQAns(int cid, int answer) 
{
    int i;
    String dest;
    File wstats;
  File stats  = SD.open("/etc/mcqans", FILE_READ);
  if (!stats) {
        debugLog(F("addMCQAns Open error of /etc/mcqans"));
        beep(2000);
        // cant do much now..
        return;
    }
    for (i=0; i!= MCQARRAYSIZE; i++) {
      mcqbuf[i] = 0;  
  }
  stats.read((uint8_t *) &mcqbuf[0], MCQARRAYSIZE);     

 DeserializationError error= deserializeJson(mcqBuffer, &mcqbuf[0]);
   if (error) {
              debugLog(F("AddMCQAns deserializeJson() failed with code "));
              debugLogln(error.c_str());
              wifi = false;
    }
    Serial.print("Contents of mcqans:");
         JsonArray v = jsonBuffer.as<JsonArray>();
            for(JsonVariant c : v) {
 
       Serial.print("cid:"); Serial.print((int)  c["cid"], DEC); Serial.print("ans:"); Serial.print((int) c["ans"], DEC); 
       Serial.print(" ");
     }

JsonObject newentry = mcqBuffer.createNestedObject();
newentry["cid"] = cid;
newentry["ans"] = answer;
serializeJson(mcqBuffer, Serial);
serializeJson(mcqBuffer, dest);
     Serial.print("dest is:"); Serial.println( dest.c_str());
     Serial.print("After printo:"); Serial.print((int)dest.length());
     stats.close();
     
     wstats = SD.open("/etc/mcqans", FILE_WRITE);
     wstats.write((uint8_t *) dest.c_str(), dest.length());
     
     wstats.close();

     
}


File onf(File dir)
{
  String fname;  
  fib_t fib;
  int i;
  int j;
  
  Serial.print("onf:"); Serial.println(dir.name());
  if (leafdir) {
     //j = totalCids - 1;
    j = totalCids;
    Serial.println("onf:leafdir");Serial.print("CidIndex:"); Serial.println(cidIndex);
    if (cidIndex == j) {
     // cidIndex = 0;
        Serial.println("!");
        return (File) NULL;
    }
    cid = cidArray[cidIndex];
    cidIndex++;
    fname = dir.name();
    fname.concat("/");
    fname.concat(cid);
    Serial.print("fname is:"); Serial.println(fname);
    onfnext.close();
    onfnext = SD.open(fname, FILE_READ);        // change 2409
    
    onfnext.read((uint8_t *) &fib, sizeof(fib_t));
    currentCid = fib.cid;
    currentCtype = fib.ctype;
 //   currentLastRead = fib.lastread;
    if (currentCtype == 3) {    // for tests, we always start at beginning, no last read
      currentLastRead = sizeof(fib_t);
    } else {
      currentLastRead = getLastRead(currentCid);
    }
    Serial.print("currentCid:"); Serial.println(currentCid);
    Serial.print("currentCtype:"); Serial.println(currentCtype);
    Serial.print("currentLastRead:"); Serial.println(currentLastRead);
    // zero the currenttitle

    for (i=0; i!= 14; i++) {
      currentTitle[i] = 0;
    }
    for (i=0; i!= 14; i++ ) {
          if (fib.title[i] == 0x0) {
            break;
          }  
         currentTitle[i] = fib.title[i];     // copy the title
    }
    return onfnext;
  }

  return dir.openNextFile();
}

File opf(File dir)
{
  String fname;
  File next;
  int i;
  fib_t fib;

  
  Serial.print("opf:"); Serial.println(dir.name());
  if (leafdir) {
    Serial.print("leafdir"); Serial.print("CidIndex:"); Serial.println(cidIndex);
    if (cidIndex == 0) {
       Serial.println("@");
       return (File) NULL;
     // cidIndex = totalCids;
    }
    cidIndex--;
    cid = cidArray[cidIndex];
    
    fname = dir.name();
    fname.concat("/");
    fname.concat(cid);
    Serial.print("fname is:"); Serial.println(fname);
    next = SD.open(fname, FILE_READ);       // change 2409
    next.read((uint8_t *) &fib, sizeof(fib_t));
    currentCid = fib.cid;
    currentCtype = fib.ctype;
    if (currentCtype == 3) {    // for tests, we always start at beginning, no last read
      currentLastRead = sizeof(fib_t);
    } else {
      currentLastRead = getLastRead(currentCid);
    }
 //   currentLastRead = fib.lastread;

    // zero the currenttitle

    for (i=0; i!= 14; i++) {
      currentTitle[i] = 0;
    }
    for (i=0; i!= 14; i++ ) {
          if (fib.title[i] == 0x0) {
            break;
          }  
         currentTitle[i] = fib.title[i];     // copy the title
    }
    return next;
  }
  return dir.openNextFile();
}

unsigned long getLastRead(int cid)
{
   int i;
   unsigned long pos;
   
   File lastread  = SD.open("/etc/lastread", FILE_READ);
   
    if (!lastread) {
          debugLog(F("getLastRead Open error of /etc/lastread"));
          beep(2000);
          return sizeof (fib_t);
      }

    for (i=0; i!= LASTREADARRAYSIZE; i++) {
      lastreadbuf[i] = 0;
    }
  
  lastread.read((uint8_t *) &lastreadbuf[0], LASTREADARRAYSIZE);     
  bool found = false;
  
 DeserializationError error= deserializeJson(lastReadBuffer, &lastreadbuf[0]);
   if (error) {
              debugLog(F("getLastRead deserializeJson() failed with code "));
              debugLogln(error.c_str());
              return sizeof(fib_t);
    }
    Serial.print("Contents of lastread:");
         JsonArray v = lastReadBuffer.as<JsonArray>();
            for(JsonVariant c : v) {
       
       Serial.print("cid:"); Serial.print((int)  c["cid"], DEC); Serial.print(" lr"); Serial.print((int) c["lr"], DEC); 
       Serial.print(" ");
       if ((int) c["cid"] == cid) {
        pos = c["lr"];
        Serial.println("Found match");
        found = true;
       }
     }

    if (!found) {
     return sizeof(fib_t);
    } else {
     return pos;
    }
    lastread.close();
}

void handleN1()
{
  int timeinsecs;
 
  int i;
  int j;

  debugLogln("N1");
  if (waitforakey) {
    if (fileDeleted) {
       reloadCurrRoot();
    }
    waitforakey = false;
     menuLevel = 0;
     cmdIndex = 0;                        // displays books
     displayCmd(cmdIndex);
    return;
    
  }

  if (mcqAnswerOn) {
    mcqAnswer = 0;
    mcqAnswerOn = false;
    addMCQAns(currentCid, 0);
    beep(200);
    delay(100*divider);
    beep(200);
    // continue to handle as if N1 was pressed!! cool
    
  }
  if ((cmdMode) && menuLevel ==0) {
    // already in top menu.. just beep and stay
    beep(200);
    return;
  } 

  // come here if in cmdMode but different menulevel (1,2,3) -> make it menulevel as 0 and return
  if (cmdMode) {
    // already in menu mode, now go to top level menu
    menuLevel = 0;
    cmdIndex = 0;
    displayCmd(cmdIndex);
    return;
  }

  /*
   * come here if not cmdMode..
   */
  
   if (!cmdMode) {
     if ((!strcmp(root.name(), "/cc")) || (!strcmp(root.name(), "/nc"))) {
      Serial.println("Going back to cmd mode");
      cmdMode = true;
       menuLevel = 0;
       cmdIndex = 0;
       displayCmd(cmdIndex);
      return;
     }
   }

   
   if (!pop()) {
        Serial.println(F("Beep"));
        beep(200);
        return;
      } 
    if (fileopen) {  
        fileopen = false;
        language = 'e';
        curLine = 0;              // when we close the file, reset the curLine also. it starts again at 0

        for (i=0; i!= LASTREADARRAYSIZE; i++) {
            lastreadbuf[i] = 0;  
        }
        
       File lastread  = SD.open("/etc/lastread", FILE_READ);
        if (!lastread) {
              Serial.print(F("handleN1 Open error of /etc/lastread"));
              beep(2000);
              // cant do much now..
              return;
          }
          
  lastread.read((uint8_t *) &lastreadbuf[0], LASTREADARRAYSIZE);     
  bool found = false;
  
 DeserializationError error= deserializeJson(lastReadBuffer, &lastreadbuf[0]);
   if (error) {
              debugLog(F("handleN1 LastreadBuf deserializeJson() failed with code "));
              debugLogln(error.c_str());
              return;
    }
    Serial.print("Contents of lastread:");
         JsonArray v = lastReadBuffer.as<JsonArray>();
            for(JsonVariant c : v) {
       
       Serial.print("cid:"); Serial.print((int)  c["cid"], DEC); Serial.print(" lr"); Serial.print((int) c["lr"], DEC); 
       Serial.print(" ");
       if ((int) c["cid"] == currentCid) {
        j = curr.position() - 14;
        if (j < sizeof(fib_t)) {
          j = sizeof(fib_t);
        }
         c["lr"] = j;     // TODO: hardcoded length of braile line
        Serial.print("*Found match: writing lr:"); Serial.println((int) c["lr"]);
        found = true;
       }
     }

    if (!found) {
      JsonObject newentry = lastReadBuffer.createNestedObject();
      newentry["cid"] = currentCid;
      j = curr.position() - 14; // TODO: hardcoded length of braile line
       if (j < sizeof(fib_t)) {
          j = sizeof(fib_t);
        }
         newentry["lr"] = j;     // TODO: hardcoded length of braile line
       Serial.print("Writing lr"); Serial.println((int) newentry["lr"]);
    }
    
    String dest;
    
    serializeJson(lastReadBuffer, Serial);
    serializeJson(lastReadBuffer, dest);
     Serial.print("dest is:"); Serial.println( dest.c_str());
     Serial.print("After printo:"); Serial.print((int)dest.length());
     lastread.close();
     
     File lr = SD.open("/etc/lastread", FILE_WRITE);
     lr.write((uint8_t *) dest.c_str(), dest.length());
     lr.close();



        
        // additions over
   //     root.close();
        
        root =  popped;
         debugLog("closing "); debugLogln(curr.name());
 //       curr.close();       // 2510

        // find time used in reading the file
        endtime = millis();
        Serial.print("starttime:"); Serial.println(starttime);
        Serial.print("endtime:"); Serial.println(endtime);
        timeinsecs = (endtime-starttime)/1000;
        if (timeinsecs == 0) {
          timeinsecs = 1;           // round off in rare case of less than 1 sec!
        }
        addStats(currentCid, timeinsecs);

        currentCid = 0;             // reset it as file is getting closed now

      saved = curr;
      curr = onf(root);
      if (curr == NULL) {
        curr = saved;
        Serial.println("%");
      }
      dirCursor = 1;
      printdir((char *) curr.name(), curr.isDirectory());        // XXX
      return;
      }

      leafdir = false;
       root.close();      // otherwise it causes memory leak!
      curr.close();       // otherwise it causes memory leak!
      root =  popped;
      root.rewindDirectory();
      curr = onf(root);
      dirCursor = 1;
      Serial.println(curr.name());
      printdir((char *) curr.name(), curr.isDirectory());        // XXX
      return;   
}

void handleN4()
{

  
   if (waitforakey) {
    if (fileDeleted) {
      reloadCurrRoot();
    }
    waitforakey = false;
     menuLevel = 0;
     cmdIndex = 0;
     displayCmd(cmdIndex);
    return;
    
  }
  
  if (mcqAnswerOn) {
    mcqAnswer = 2;
    mcqAnswerOn = false;
    addMCQAns(currentCid, 2);
     beep(200);
     delay(100*divider);
    beep(200);
      handleN1();
    return;
    
  }
  
   if (cmdMode) {
    switch (menuLevel) {
      case 0: // top level menu
        if (cmdIndex == NO_OF_TOP_LEVEL_CMDS-1) {
            beep(200);
            return;
        } else {
          cmdIndex++;
        }
        break;
      case 1:
         if (cmdIndex == NO_OF_CONNECT_CMDS-1) {
            beep(200);
            return;
 //         cmdIndex = 0;
        } else {
          cmdIndex++;
        }
        break;
       case 2:
         if (cmdIndex == NO_OF_SETUP_CMDS-1) {
            beep(200);
            return;
        } else {
          cmdIndex++;
        }
        break;
       case 3:
         if (cmdIndex == NO_OF_CHECKHEXIS_CMDS-1) {
            beep(200);
            return;
 //         cmdIndex = 0;
        } else {
          cmdIndex++;
        }
        break;
    }
    displayCmd(cmdIndex);
    return;
   }

   
   if (fileopen) {
        if (autonextline) {
          autonextlineCounter = 0;        // reset the counter to let read new line properly
        }
       Serial.println("fileopen");
        nextline();
        return;
      }

    /* no file open */
    saved = curr;
    curr = onf(root);
    
    if (!curr)
    {
        beep(200);
        curr = saved;
        return;
 //@    Serial.print("no more files, rewinding");
 //@    root.rewindDirectory();
 //@    dirCursor = 1;
 //@    curr = onf(root);
     
   } else {
    dirCursor++;
   }
    Serial.println((curr.name()));
   printdir((char *) curr.name(), curr.isDirectory());        // XXX
   return;
} 


/*
 * Long press N1 - takes to remote debug mode
 */
void handleN5()
{
  String t;
  debugLogln("N5");
  if ((cmdMode) &&(menuLevel == 0)) {
    // if N5 is pressed in command mode and root level, then go to remote debug mode. cannot come out of this mode
    Serial.println("entering remotedebug");
  //  remoteDbg();
    uploadLogFlag = true;
       
       // debuglog the configuration details

     t = "Contraction:";
     if (contractMode) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     
     t += "Autoscroll:";
     if (autonextlinemode) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     
     t += "Always connected:";
     if (alwaysON) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     
     t += "Software ver:";
     t += versionDetails;
     t += "\n";
     t += "Cell stack ver: 1.0\n";
     t += "Student ID:";
     t += hexisId;
     t += "\n";
     t += "Start heap:";
     t += ESP.getFreeHeap();
     t += "\n";

     debugLogln(t);
     
  }
}

/*
 * long press N2 - takes to test sequence printing
 */
void handleN6()
{
  debugLogln("N6");
  if (fileopen) {
    curr.seek(sizeof(fib_t));
    Serial.println("Reset seek");
    nextline();
    return;
  }
  
  if ((cmdMode) &&(menuLevel == 0)) {
  
    // if N5 is pressed in command mode and root level, then go to remote debug mode. cannot come out of this mode
    Serial.println("setting testSeq");
    testSeqFlag = true;
//    ff00 = true;
    return;
  }
}

/*
 * long press N4 - takes to test sequence printing
 */
void handleN8()
{
  debugLogln("N8");
  if ((cmdMode) &&(menuLevel == 0)) {
  
    // if N5 is pressed in command mode and root level, then go to remote debug mode. cannot come out of this mode
    Serial.println("setting ff00");  
    ff00 = true;
    return;
  }
}

/*
 * Long press N3 - deletes current file
 */
void handleN7()
{
  String fname, cidSt, folder;
  int cid;
  int index;
 debugLogln("N7");
  Serial.print("Cmdmode:"); Serial.println(cmdMode);
  if (!cmdMode) {
    // if not in command mode, it means to delete the current file
    if (curr.isDirectory()) {
      Serial.println("dir");
      Serial.println("not deleting...");
    } else {
       Serial.println("file");
       //first delete non contract file..
      fname = curr.name();
      fname.setCharAt(1, 'n');
      Serial.print("deleting..."); Serial.println(fname);
      SD.remove(fname);
      // remove contract file now
      fname.setCharAt(1, 'c');
       Serial.print("deleting..."); Serial.println(fname);
      SD.remove(fname);

      // get CID from fname
      index = fname.lastIndexOf('/');       // cid is after last /
      cidSt = fname.substring(index+1);
      cid = cidSt.toInt();
      Serial.println("CID to be deleted is:"); Serial.println(cid);
      folder = fname.substring(0, index+1);
      fname.setCharAt(1, 'c');
      Serial.println("folder name is:"); Serial.println(folder);
      
      beep(200);
   
      
     /*
      * Close current pointer, and go back to root just as a precaution after okay
      * 
      */
     printLine(okay);
     fileDeleted = true;
     waitforakey = true;
    }
  }
}


void handleN2()
{
  int i;
  debugLogln("N2");
     Serial.print("cmdMode:"); Serial.print(cmdMode);
   Serial.print("menuLevel:"); Serial.print(menuLevel);
    Serial.print("cmdIndex:"); Serial.print(cmdIndex);

    if (waitforakey) {
      if (fileDeleted) {
        reloadCurrRoot();
    }
    waitforakey = false;
     menuLevel = 0;
     cmdIndex = 0;
     displayCmd(cmdIndex);
    return;
    
  }
  
   if (mcqAnswerOn) {
    mcqAnswer = 1;
    mcqAnswerOn = false;
    addMCQAns(currentCid, 1);
     beep(200);
     delay(100*divider);
    beep(200);
      handleN1();
    return;
    
  }
  
    if (cmdMode) {
      if (cmdIndex == 0 ) {
          beep(200);
          return;
        } else {
          cmdIndex--;
        }
         Serial.print("cmdIndex:"); Serial.print(cmdIndex);
      displayCmd(cmdIndex);
      return;
    }

    
    if (fileopen) {
        if (autonextline) {
          autonextlineCounter = 0;        // reset the counter to let read new line properly
        }
        prevline();
        return;
    }

    if (leafdir) {
      saved = curr;
      curr = opf(root);
        if (!curr) {
          beep(200);
          curr = saved;
          return;
        }
      printdir((char *) curr.name(), curr.isDirectory());        // XXX
      return;
    }
    Serial.print("root is"); Serial.println(root.name());
    Serial.print("curr is"); Serial.println(curr.name());

    Serial.print("dirCursor is:"); Serial.println(dirCursor);

    if (dirCursor == 1) {
      Serial.println("oops");
      beep(200);
      return;
    }
     root.rewindDirectory();
        for (i = 0; i != dirCursor-2; i++) {   //??
         next = root.openNextFile(); 
         next.close();
        }
      //curr.close();     //2310
      curr = root.openNextFile(); 
        Serial.println(next.name());
         printdir((char *)curr.name(), (bool) curr.isDirectory());
         dirCursor--;
}

void handleN3() {

  bool changed = false;
  int attempts = 0;
  
  debugLogln("N3");
 Serial.print("cmdMode:"); Serial.print(cmdMode);
   Serial.print("menuLevel:"); Serial.print(menuLevel);
    Serial.print("cmdIndex:"); Serial.print(cmdIndex);
   if (waitforakey) {
    if (fileDeleted) {
       reloadCurrRoot();
    }
    waitforakey = false;
     menuLevel = 0;
     cmdIndex = 0;
     displayCmd(cmdIndex);
    return;
    
  }

  // root level commands..
  
  if ((cmdMode) && (menuLevel == 0)) {
      switch(cmdIndex) {
        case 0:
          if (contractMode) {
          openRoot("/cc");
        } else {
          openRoot("/nc");
        }
          cmdMode = false;
          cmdIndex = 0;
          break;
        case 1:
          menuLevel = 1;
          cmdIndex = 0;
          displayCmd(0);
          break;
        case 2:
          menuLevel = 2;
          cmdIndex = 0;
          displayCmd(0);
          break;
         case 3:
          menuLevel = 3;
          cmdIndex = 0;
          displayCmd(0);
          break;
      }
     return;
    }
    
    // come here if connect commands
      if ((cmdMode) && (menuLevel == 1)) {
    switch (cmdIndex) {
    case 0:
         printLine(downloading);
        if (fetchContent()) {
            if (contentCount == 0) {
            printLine(nonew);
          } else {
            printLine(done);
          }
        }
        delay(250*divider);
        waitforakey = true;
        break;
      case 1:
        printLine(uploading);
        fetchContent();
        printLine(uploaded);
        delay(250/divider);
        waitforakey = true;
        break;
   } 
   return;
      }

        // come here if setup commands
        
     if ((cmdMode) && (menuLevel == 2)) {
    switch (cmdIndex) {
      case 0:
          Serial.println("Deleting all files");
          deleteAll();
          printLine(okay);
           waitforakey = true;         
          break;
      case 1:
          Serial.println("on your mobile browser, type vembi.in/wifi");
          changePassword();
          waitforakey = true;
          break; 
       case 2:
        Serial.println("autonext slow");
        autonextlinemode = true;
        autonextlinespeed = SLOW;
        changed = true;
        printLine(okay);
        waitforakey = true;
        break;
       case 3:
      Serial.println("autonext fast");
        autonextlinemode = true;
        autonextlinespeed = FAST;
        changed = true;
        printLine(okay);
        waitforakey = true;
        break;   
      case 4:
        Serial.println("Autoscroll OFF");
        autonextlinemode = false;
        changed = true;
        printLine(okay);
        waitforakey = true;
        break;
      case 5:
        Serial.println("Contractions ON");
        contractMode = true;
        changed = true;
        printLine(okay);
        waitforakey = true;
        break;
      case 6:
         Serial.println("Contractions OFF");
         contractMode = false;
         changed = true;
          printLine(okay);
          waitforakey = true;
          break; 
      case 7:
          Serial.println("word wrap on");
            printLine(okay);
          wordwrap = true;
          waitforakey = true;
           changed = true;
          break;
      case 8:
          Serial.println("word wrap off");
           printLine(okay);
            wordwrap = false;
          waitforakey = true;
           changed = true;
          break;
    }
    if (changed) {
      changed = false;

      /*
       * write the changed config to /etc/cfg file
       */
      File file = SD.open("/etc/cfg", FILE_WRITE);
      cfgBuffer["autoscroll"] = autonextlinemode;
      cfgBuffer["autonextlinespeed"] = autonextlinespeed;
      cfgBuffer["contract"] = contractMode;
      cfgBuffer["alwayson"] = alwaysON;
      cfgBuffer["wordwrap"] = wordwrap;
      Serial.print(" Writing new cfg values:"); serializeJson(cfgBuffer, Serial);
      serializeJson(cfgBuffer, file);
      file.close();

    }
    return;
  }
  
   // come here if check hexis level commands
    if ((cmdMode) && (menuLevel == 3)) {
    switch (cmdIndex) {
      case 0:
        printLine(checking);
        WiFi.begin(ssid, password);
        while (WiFi.status() != WL_CONNECTED) {
          attempts++;
          if (attempts == MAX_ATTEMPTS) {
            break;
          }
          delay(1000*divider);
          debugLogln("CC: Connecting to WiFi..");
        }
        if (attempts == MAX_ATTEMPTS) {
          printLine(connfailed);
        } else {
          printLine(connokay);
        }
        delay(250);
         WiFi.mode(WIFI_OFF);
        waitforakey = true;  
        break;
    
      case 1:
          Serial.println("battery");
          if (readBatteryVoltage()) {
            printLine(normal);
          } else {
            printLine(low);
          }     
           waitforakey = true;
          break; 
      case 2:
          Serial.println("factory reset");
          resetFactoryValues();
          printLine(okay);
           waitforakey = true;
          break; 
    }
    return;
  }
  
  if (fileopen) {
    if (currentCtype == 3) {      //TODO: hardcoded to MCQ
    // MCQ is open and N4 pressed, then enter the MCQ answer mode
    Serial.println("Setting mcqAnswerON");
    beep(100);
    mcqAnswerOn = true;
    return;
    }
    // else
    
    beep(200);
    return;             // if file is open, no meaning for N4
  }
  // come here if not in command mode - open file..
  push(root); 
  selectFunc();
}

void resetFactoryValues()
{
  File file = SD.open("/etc/cfg", FILE_WRITE);
  String nulljson = "[]";
  
      cfgBuffer["autoscroll"] = false;
      cfgBuffer["autonextlinespeed"] = autonextlinespeed;
      cfgBuffer["contract"] = false;
      cfgBuffer["alwayson"] = false;
      cfgBuffer["wordwrap"] = false;
      cfgBuffer["wifiap"] = "hexis";
      cfgBuffer["wifipw"] = "hexis123";
      Serial.print(" Writing new cfg values:"); serializeJson(cfgBuffer, Serial);
      serializeJson(cfgBuffer, file);
      file.close();

  // zero out all other files like stats, lastread..

   File lr = SD.open("/etc/lastread", FILE_WRITE);
     lr.write((uint8_t *) nulljson.c_str(), nulljson.length());
     lr.close();

    File  ls = SD.open("/etc/stats", FILE_WRITE);
     ls.write((uint8_t *) nulljson.c_str(), nulljson.length());
     ls.close();
     
    File lm = SD.open("/etc/mcqans", FILE_WRITE);
     lm.write((uint8_t *) nulljson.c_str(), nulljson.length());
     lm.close();
}
#if 0
void remoteDbg()
{
 
  
   // connect the esp32 to the desired access point
  myBot.wifiConnect(ssid, password);
  
  // set the telegram bot token
  myBot.setTelegramToken(token);
  // check if all things are ok
  if (myBot.testConnection())
    Serial.println("\ntestConnection OK");
  else
    Serial.println("\ntestConnection NOK");

  
  while(1) {      // now we are in this loop till reset.
  // if there is an incoming message...
  if (myBot.getNewMessage(msg) != CTBotMessageNoData)
    // ...forward it to the sender
    Serial.print("sender:");
    Serial.println(msg.sender.id);
    if (msg.sender.id != CHAT_ID) {
      Serial.println("wrong user!");
    }
    Serial.print("msg ID");
    Serial.println(msg.messageID);
    if (msg.messageID != prevMessageID) {       // to handle the bug in CT library.. TODO
         processMsg(msg);
         prevMessageID = msg.messageID;
    }
  // wait 500 milliseconds
  delay(2000*divider);
  
}
}


/*
 * Command line processing of telegram commands
 */
void processMsg(TBMessage msg)
{
    String text = msg.text;
    String t;
  

    if (text == "/debug")
    {
     debugLog("Free memory: "); 
     debugLogln(String(ESP.getFreeHeap()));
     debugLog("On time: "); 
     debugLog(String(onCtr/5)); 
     debugLogln("seconds");
     debugLog("Battery voltage: "); debugLog(String( readBatteryVoltage())); debugLogln("V");
     myBot.sendMessage(msg.sender.id,debugInfo);
    }
     if (text == "/cfg")
    {
     t = "Contraction:";
     if (contractMode) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     t += "Autoscroll:";
     if (autonextlinemode) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     t += "Always connected:";
     if (alwaysON) {
      t += "On\n"; 
     } else {
      t += "Off\n";
     }
     t += "Software ver:";
     t += versionDetails;
     t += "\n";
     t += "Cell stack ver: 1.0\n";
     t += "Student ID:";
     t += hexisId;
     

     myBot.sendMessage(msg.sender.id,t);
    }

    if (text == "/start")
    {
      String welcome = "Welcome to Hexis\n";
      welcome += "/setsid xx : to set new student ID xx\n";
      welcome += "/debug : dump present debug info\n";
      welcome += "/cfg: dump configuration info\n";
      myBot.sendMessage(msg.sender.id, welcome);
    }
    
    int ind = text.indexOf(' ');  //finds location of first space
    t = text.substring(0, ind);   //captures first data String
      Serial.println(t);
    if (t == "/setsid")
    {
      hexisId = text.substring((ind+1)).toInt();
      Serial.print("new SID is:");
      Serial.println(hexisId);
      myBot.sendMessage(msg.sender.id, "set the new student ID");

      // change in cfg file now

    cfg = SD.open("/etc/cfg", FILE_WRITE);
    cfg.read((uint8_t *) &cfgbuf[0], CFGARRAYSIZE);
    DeserializationError error= deserializeJson(cfgBuffer, &cfgbuf[0]);
    if (error) {
              debugLog(F("/etc/cfg deserializeJson() failed with code "));
              debugLogln(error.c_str());
              // TODO: what to do now? 
    }
    cfgBuffer["hexisId"] = hexisId;
    serializeJson(cfgBuffer, cfg);
    cfg.close();
    }
    
}
#endif


void printLine(const char * str)
{
  int i;
  Serial.println("In PL");
  for (i=0; i!=14; i++) {
    inp[i] = 0x0;
  }
  i = 0;
  while (*str != 0) {
    inp[i] = convtocode(*str);
    str++; 
    i++;
  }

  displine();

}

void printLongLine(const char * str)
{
  int i;
  Serial.println("In PL");
  for (i=0; i!=14; i++) {
    inp[i] = 0x0;
  }
  i = 0;
  while (*str != 0) {
    inp[i] = convtocode(*str);
    str++; 
    i++;
  }

  displine();

}
/*
 * Key 3 (select) handler
 */

void selectFunc()
{
  File temp;
 
  String fname, cidSt;
  int cid, index;
  int i = 0;
 
 
  
  Serial.println("In SelectFunc");
  Serial.print("curr is:"); Serial.println(curr.name());
  debugLog("opening "); debugLogln(curr.name());
  
  if(curr.isDirectory())
  {

    // check for empty directory first
        temp = onf(curr);
    if (temp == NULL) {
          Serial.println("empty directory!");
          beep(100);
          delay(100*divider);
          beep(100);
          temp.close();
          return;
    }
  
      // check if this is a leaf directory
      Serial.println(temp.name());
      
 //     temp = onf(curr);
      if (!temp.isDirectory()) {
        // it is a leaf directory!

    leafdir = true;
    Serial.println("leafdir");

    // zero out the cid array

    for (i=0; i!=CIDARRAYSIZE; i++) {
      cidArray[i] = 0;
    }
    cidIndex = 0;
    
    Serial.println("printing all names..");
    Serial.println(temp.name());
   

    i = 0;
    fname = temp.name();
    index = fname.lastIndexOf('/');       // cid is after last /
    cidSt = fname.substring(index+1);
    cid = cidSt.toInt();
    cidArray[i] = cid;
    temp.close();
    i++;
      
    while (true) {
      temp = curr.openNextFile();
      if (temp == NULL) {
        break;
      }
      
      fname = temp.name();
      index = fname.lastIndexOf('/');       // cid is after last /
      cidSt = fname.substring(index+1);
      cid = cidSt.toInt();
      Serial.println(cid);

      // now insert to the array
      cidArray[i] = cid;
      i++;
      temp.close();

    }
    
    // now sort it and keep it ready
    sortArrayReverse(cidArray, i);
    totalCids = i;
    printArray(cidArray, i+1);  
    }
     
     //root.close();        //2310
     root = curr;
     Serial.println("Opening directory");
     curr = onf(curr);
     printdir((char *) curr.name(), curr.isDirectory());        // XXX

   /*
    Serial.println(curr.name());
   */
    dirCursor = 1;
   /* code to add path */
  } else {
    
   
    /*
     * seek to lastread position
     */
    Serial.print("starting at last read pos"); Serial.println(currentLastRead);
    curr.seek(currentLastRead);      
    
    fileopen = true;

    // load the autonextline value

    autonextline = autonextlinemode;

    /*
     * Start timer for stats
     */
    starttime = millis();
    nextline();

    return;
   
  }
 
}
  

void printArray(int* myArray, int sz) {

int i;
  Serial.print("Sorted array");
  for (i=0; i!= sz; i++) {
    Serial.print(myArray[i]);
  }
}
/*
 * Print directory name or file name from title
 */
void printdir(char *temp, bool isDir) {

  int i;
  char *s;
  String t(temp);
    Serial.print("in PD:"); Serial.println(temp);
   for (i = 0; i != 14; i++) {
    inp[i] = 0x0;
   }
   if (isDir) {

    /*
     * first get the directory name only, remove full path
     */
  
    inp[0] = 0xff;
    int lastslash = t.lastIndexOf('/');
    s = temp+lastslash+1;
    for (i=0; i!= 14; i++) {
      Serial.print(*s);
      inp[i+1] = convtocode(*s);
      if (*s == '\0')
        break;
      s++;
    }
    Serial.println("");

   } else {
    inp[0] = 0x0;        // hello
    Serial.print("title:");
    for (i=0; i!=14; i++) {
      if (currentTitle[i] == 0x0) {
        break;
      }
      Serial.print(currentTitle[i]);
      inp[i+1] = convtocode (currentTitle[i]);
    }
    Serial.print("Path:"); Serial.println(temp);
   }
   
   displine();
}

uint8_t convtocode(char c)
{
    c |= 0x020;       // lowercase all directory and file names
  for (int i=0; i < sizeof(chars); i+=1)
  {
      if (c == chars[i])
    { 
 //         Serial.print("found:"); Serial.print(char(chars[i])); Serial.print(" "); Serial.print(hexes[i], HEX);
          return hexes[i];
    }
  }
}

void nextline() {
   int i;
   int ret;
   int j;
   int k;
   int a;


  
  Serial.print("nextline:pos:"); Serial.println(curr.position());
  for (i=0; i !=14; i++) {
  temp[i] = 0x0;         // hello
 }
  if (!curr.available()) {
  Serial.print("EOF");
  autonextline = false;
  autonextlineCounter = 0;
  beep(100);
  // we have reached end of file, so last read can be put back as beginning..
  
  return;
 }
 ret = curr.read((unsigned char *) temp, 14); 

 Serial.print("nextline:");
 for (i=0; i!=14; i++) {
   Serial.print(temp[i], HEX); Serial.print(" ");
 }


 if (wordwrap && fileopen) {
    for (k = 0; k !=14; k++) {
      a = temp[13-k];
      if ((a == 0x00) || (a == FULLSTOP_BRAILLE) || (a == COMMA_BRAILLE) ||(a == SEMICOLON_BRAILLE)) {
        break; 
      } 
    }

  Serial.print(" k:"); Serial.println(k, HEX);
  
    // zero out the last characters that split

 
    if (k != 14) {
      for (j = 0; j !=k ; j++) {
          temp[13-j] = 0x00;      // space
        }
        curr.seek(curr.position() - k);
  }

    // copy the parsed line to buffer

    Serial.print("curLine:"); Serial.println(curLine);
    for (j=0; j!= 14; j++) {
       Serial.print(temp[j], HEX); Serial.print(" ");
      parsedLines[curLine][j] = temp[j];
    }
    curLine++;
 }
 
 if (hyphenOn) {
   if (temp[13] != 0x00) {  // space
    if (temp[12] == 0x00) {
      curr.seek(curr.position() -2);
      temp[12] = 0x0;
      temp[13] = 0x0;
    } else {
      temp[13] = 0xc;   // braille code for hyphen
      curr.seek(curr.position() - 1);
      }
    }
 }
//  DP(F("Read:"), CE_DBG_FLAG);
 for (i=0;i!=14;i++) {
 // Serial.print(temp[i], HEX);
  inp[i] = temp[i];
 }
 
 displine();
}


void prevline() {

  unsigned long pos = 0;
   int i, j, k;
   int f;
   int a;
  

    for (i=0; i !=14; i++) {
  temp[i] = 0x0;             // hello
 }

 if (wordwrap && fileopen) {
    if (curLine == 0) {
      beep(200);
      return;
    }
    // copy already parsed line and display
    Serial.print("curLine:"); Serial.println(curLine);
    
    for (j=0; j!=14; j++) {
      inp[j] = parsedLines[curLine-1][j];
    }
    curLine--;
    displine();
    return;
 }
 
  pos = curr.position();
  Serial.print("pos:"); Serial.println(pos);
  if (pos <= (sizeof(fib_t) + 14)) {        // TODO: kludge. wont work for short files
    beep(100);
    return;
  }


  a = pos-28;
  if (a < sizeof(fib_t)) {
    a = sizeof(fib_t);
  }
  curr.seek(a);
   curr.read((unsigned char *) temp, 14);
 Serial.print("prevline:");
 for (i=0; i!=14; i++) {
   Serial.print(temp[i], HEX); Serial.print(" ");
 }



 
    // for now it is disabled.
 if (hyphenOn) {
   if (temp[13] != 0x00) {  // space
    if (temp[12] == 0x00) {
      curr.seek(curr.position() -2);
      temp[12] = 0x0;
      temp[13] = 0x0;
    } else {
      temp[13] = 0xc;   // braille code for hyphen
      curr.seek(curr.position() - 1);
      }
    }
 }
   for (i=0;i!=14; i++) {
  //   Serial.print(temp[i]);
     inp[i] = temp[i];
    }
    displine();
}



void push(File d) {

  Serial.print("PUSHING:"); Serial.println(d.name());
  if (top >= STACKSIZE) {
    Serial.println(F("Stack overflow push!"));
    return;
  }
  top++;
  stack[top] = d;
  
}

int pop() {

  if (top <= -1) {
    Serial.println(F("Stack overflow pop!"));
    return 0;
  }
  popped= stack[top];
  Serial.print("POPPED:"); Serial.println(popped.name());
  top--;
  return 1;
}

/* 
 *  Cell specific driver codes
 */

void brailledisplay(uint8_t *disp)
{
  uint8_t i;

  uint8_t bufferSize = sizeof(tempdisprev);
  clearTempBuffer();
  memcpy(tempdisprev, disp, bufferSize);
  memcpy(tempdisprevInverted, tempdisprev, bufferSize);
 
 mirrorOddByteLowNibble(tempdisprev, bufferSize);
  for (i = 0; i < bufferSize; i++) {
    tempdisprevInverted[i] = (~tempdisprev[i]) & 0xFF;
  }
  
  
  uint8_t index;


for (index = 0; index !=20; index++) {
   fire(index);
    }

  /*
   * now save this line as prev line
   */
for (index = 0; index !=20; index++) {
  prev[index] = tempdisprev[index];
}

}

//  This routine below flips 4 bits of data. The motors on the left half and right half of the cell have opposite direction of rotation for logic display.
void mirrorOddByteLowNibble(uint8_t *disp, uint8_t bufferSize) {
  uint8_t i = 0;
  uint8_t temp = 0;
  for (i = 0; i < bufferSize; i++) {
    temp = *(disp + i);
    if (i % 2 != 0) {
      *(disp + i) = ((temp & 0x0A) >> 1) | ((temp & 0x05) << 1) | (temp & 0xF0);
    }
  }
}

/*
 * this routine actually fires the cells.
 * After many rounds of finetuning, testing, here are the key points:
 *  1. first firing has to be around 20msec. otherwise, moment of inertia does not take it moving
 *  2. we need atleast 3, preferably 4 sets of firings with reduced timings for firing. This will handle the throwback issues.
 *  3. there is a time needed between 2 firings, for battery to recoup. 
 *  4. Working combo is 20-2, 5-2, 2-2, 2-0 all in msecs
 *  
 */
void fire(uint8_t index) {

  uint8_t a[20];
  uint8_t b[20];
  uint8_t i;

  if (prev[index] == tempdisprev[index]) {
    return;
  }

  
  memset(a, 0, 20);
  memset(b, 0, 20);

 
  a[index] = tempdisprev[index];
  b[index] = tempdisprevInverted[index];

  digitalWrite(STROBE1, LOW);
  for (i = 0; i < 20; i++) {
    shiftOut(DATA1, CLOCK, LSBFIRST, a[i]);//tempdisprev[i]  
    
  }
 
  digitalWrite(STROBE1, HIGH);
   
  digitalWrite(STROBE2, LOW); 
  for (i = 0; i < 20; i++) {
       shiftOut(DATA2, CLOCK, LSBFIRST,b[i]);
      
  }
  
  digitalWrite(STROBE2, HIGH);
  
   // now that all cells are strobed fire them in this loop.
    digitalWrite(OE1, LOW);   
      digitalWrite(OE2, LOW);
    delay(20); //originally 14          // firing period
      digitalWrite(OE1, HIGH);
    digitalWrite(OE2, HIGH);            // capacitance charging period to hold
    delay(2);

    digitalWrite(OE1, LOW);   
      digitalWrite(OE2, LOW);
    delay(5); //originally 14          // firing period
      digitalWrite(OE1, HIGH);
    digitalWrite(OE2, HIGH);            // capacitance charging period to hold
  delay(2); //originally 14          // firing period
  
   digitalWrite(OE1, LOW);   
      digitalWrite(OE2, LOW);
    delay(2); //originally 14          // firing period
      digitalWrite(OE1, HIGH);
    digitalWrite(OE2, HIGH);            // capacitance charging period to hold
    delay(2);
    
    digitalWrite(OE1, LOW);   
      digitalWrite(OE2, LOW);
    delay(2); //originally 14          // firing period
      digitalWrite(OE1, HIGH);
    digitalWrite(OE2, HIGH);            // capacitance charging period to hold

 
}

void dispy()
{
  int i;
  
  for(int i=0; i < 14; i++)
        {
         Serial.print(inp[i], HEX); Serial.print(" ");
        dumArray[i] = (uint8_t)~inp[i];
      }

      reverse(CHAR_LEN); 
    brailledisplay(dumArray);
    memset(dumArray, 0x0, sizeof(dumArray));
    delay(5000/divider);
}

void displine() {
  int i, j;
  char ch;
  
    debugLog("DL:");
      for(int i=0; i < 14; i++)
      {
         debugLog(String(inp[i], HEX)); debugLog(" ");
        dumArray[i] = (uint8_t)~inp[i];
      }
      for (i = 0; i <14; i++) 
      {
        for (j=0; j!= sizeof(hexes); j++) {
          if (inp[i] == 0x0) {
            ch = 0x20;
            break;
          }
          if (hexes[j] == inp[i]) {
            ch = chars[j];
            break; 
          }
        }
        Serial.print(ch);
      }
    reverse(CHAR_LEN); 
    brailledisplay(dumArray);
    memset(inp, 0x0, sizeof(inp));
    memset(dumArray, 0x0, sizeof(dumArray));
}


void clearTempBuffer() {
  uint8_t i = 0;
  while (i < 20) {
    tempdisprev[i] = 0x00;
    i++;
  }
}

void reverse(int l)
{
  int i;
  int j;
  for (i= 0, j= l-1; i< l/2; i++, j--)
  {
    uint8_t temp = dumArray[i];
    dumArray[i] = dumArray[j];
    dumArray[j] = temp;
  }
}


/*
 * true - battery voltage okay
 * false - battery needs charge
 */
bool readBatteryVoltage() 

{

  float voltage = 0.0;            // calculated voltage
  int val = 0;
  float bridge;
  float stp;

    val = analogRead(BATTERY);
    Serial.print("raw value:"); Serial.println(val);
    bridge = (float) (1.1*1024*1024.0)/(100*1024.0);
    Serial.print("bridge"); Serial.println(bridge);
    stp = 3.3/4096;
    Serial.print("step"); Serial.println(stp);
    voltage = val * stp * bridge ;
    Serial.print("voltage is:"); Serial.print(voltage);
    Serial.println (F(" V"));
    return true;            // TODO: hardcoded
    if (voltage > 3.9) {
      return true;  
    } else {
      return false;
    }
}

/*
 * Code that processes CLI commands from serial port
 */
void processCmd()

{

    int i;
    int key;
  
   
   
    char nextch;
    

    
 //    Serial.print((char) key);
   if (!Serial.available()) {
      return;
    }
    key =  Serial.read();
     Serial.print((char) key);
  switch(key) {
    case 'r':
      fetchContent();
      break;
    case 'S':
      addStats(33,3333);
      break;
    case '1':
      handleN1();
      break;
    case '4': 
      handleN4();
      break;
    case '2':
      handleN2();
      break;
    case '3':
      handleN3();
      break;
     case '5':
      handleN5();
      break;
     case '6':
      handleN6();
      break;
     case '7':
      handleN7();
      break;
     case '8':
      handleN8();
      break;
     case '9':
     {
     // cell code
      if (inp[0] == 'u') {
      for (i=0; i!=14; i++)
          inp[i] = 'c';     
    } else {
           for (i=0; i!=14; i++)
          inp[i] = 'u';     
    }
      displine(); 
      break;
     }
      case 'b': {
        beep(1000);
        break;
     }
     case 'm': {
       Serial.print("Value of MCQ answer is:"); Serial.println(mcqAnswer);
        break;
     }
     
      case 'd':  {
       while(!Serial.available());        // wait for another character!!
        debugflag = Serial.read();        // has to be 0-9
        Serial.print(F("new debug level is:")); Serial.println(debugflag);
        break;
      }
      case 'z': {
        Serial.println(debugInfo);
        break;
      }
       case 'T':  {
       while(!Serial.available());        // wait for another character!!
        nextch = Serial.read();        // 
        for (i=0; i!=14; i++) {
          inp[i] = (int) convtocode(nextch);
        }
        displine();      
        break;
      }
       case 't':  {
       testSeqFlag = true;    
        break;
      }
      case 'f':  {
      if (inp[0] == 0x0) {
      for (i=0; i!=14; i++)
          inp[i] = 0xff;     
    } else {
           for (i=0; i!=14; i++)
          inp[i] = 0x00;     
    }
        displine();
        break; 
      }
      case 'F' : {
        ff00 = true;
        for (i=0; i!=14; i++) {
          inp[i] = 0;
        }
        break;
      }
      case 'c': {
        openRoot("/cc");
        break;
      }
      case 'u': {
        openRoot("/nc");
        break;
      }
      case 'M': {
        Serial.println(ESP.getFreeHeap());
        break;
      }
      case 'X': {
        downloadFile();
        break;
      }
       
      case 'a': {
        if (autonextlinemode) {
          Serial.println("Autoscroll: OFF");
          autonextlinemode = false;
        } else {
          Serial.println("Autoscroll: ON");
          autonextlinemode = true;
        }
        break;
      }
      case 'D': {
        deleteAll();
        break;
      }
     default:
        if ((key == 0xa) || (key == 0xd)) {
          break;          // CR or LF - ignore
          
        }
        break;
     }
}


/*
 * download a file
 */

 void downloadFile()
{
    String nc = "";  
    String cc = "";
    String f = "";
    String f1 = "";
  
    int i;
    fib_t fib;
   
 
 Serial.print("df entry heap size:"); Serial.println(ESP.getFreeHeap());
 
       fib.clang = clang;
       fib.ctype = ctype;
       fib.cid = cid;
   //    fib.lastread = sizeof(fib_t);
             
     
       for (i = 0; i!=20; i++) {
        fib.title[i] = 0;       // first zero title
       }
       for (i = 0; i!= 20; i++) {     // TODO: should copy only length of title
        fib.title[i] = ctitle[i];
       }
   
            
        //String urlnc = "http://vembi.in/hexis/at/content/nc/";           // TODO: hardcoded. move to top #define
        //String urlcc = "http://vembi.in/hexis/at/content/cc/"; 
        String urlnc = String(servername) + "/content/nc/";           // TODO: hardcoded. move to top #define
        String urlcc = String(servername) + "/content/cc/"; 
    
    switch (ctype) {        // TODO:hardcoded types
              case 0x1:
               
                nc = "/nc/textbooks/";
                cc = "/cc/textbooks/";
                if (*cfolder) {
                /*
                 * check if the folder exists already, otherwise create it..
                 */
                 f = "/cc/";
                 f1 = "/nc/";
                f.concat(cfolder);
                f1.concat(cfolder);
                Serial.print("after cfolder:"); Serial.println(f);
                if (!SD.exists(f)) {
                  Serial.println("folder does not exist");
                  SD.mkdir(f);
                }
                if (!SD.exists(f1)) {
                   Serial.println("folder does not exist");
                  SD.mkdir(f1);
                }
                  
                  f.concat("/");
                 
                  f1.concat("/");
                  cc = f;
                  nc = f1;
                } else {
                  cc = "/cc/textbooks/";
                  nc = "/nc/textbooks/";
                }
                break;
              case 0x2:
                nc = "/nc/";
                cc = "/cc/";
                 if (*cfolder) {
                /*
                 * check if the folder exists already, otherwise create it..
                 */
                 f = "/cc/";
                 f1 = "/nc/";
                f.concat(cfolder);
                f1.concat(cfolder);
                Serial.print("after cfolder:"); Serial.println(f);
                if (!SD.exists(f)) {
                  Serial.println("folder does not exist");
                  SD.mkdir(f);
                }
                if (!SD.exists(f1)) {
                   Serial.println("folder does not exist");
                  SD.mkdir(f1);
                }        
                  f.concat("/");
                  f1.concat("/");
                  cc = f;
                  nc = f1;
                } else {
                   cc = "/cc/stories/";
                  nc = "/nc/stories/";
                }
                break;
              case 0x3:
               
                  cc = "/cc/tests/";
                  nc = "/nc/tests/";
                break;
     }
     nc.concat(cid); 
     cc.concat(cid);
     urlnc.concat(cid);
     urlcc.concat(cid);
     Serial.print("NC file name:");
     Serial.println(nc.c_str());
     Serial.print("CC file name:");
     Serial.println(cc.c_str());
     Serial.print("NC URL:");
     Serial.println(urlnc.c_str());
      Serial.print("CC URL:");
     Serial.println(urlcc.c_str());

    // Kludge: we save correct answer as last_read as it is not used in MCQ
     if (ctype == 3) {      //TODO: hardcoded
      Serial.print("CCA: "); Serial.println(cca);
  //    fib.lastread = cca;
     }
     
     // write FIB first

     File fdnc = SD.open(nc, FILE_WRITE);
     fdnc.write((uint8_t *) &fib, sizeof (fib_t));
     
     File fdcc = SD.open(cc, FILE_WRITE);
     fdcc.write((uint8_t *) &fib, sizeof (fib_t));
     
     http.begin(urlnc);
     http.addHeader("Content-Type", "application/x-binary");
     int httpCode = http.GET();
     if (httpCode > 0) {
       if (httpCode == HTTP_CODE_OK) {
         http.writeToStream(&fdnc);
       }
     } else {
        debugLog("[HTTP] GET... failed, error: %s\n"); debugLogln(http.errorToString(httpCode).c_str());
     } 
     Serial.println("downloaded NC file");
     fdnc.close();
     http.end();

     http.begin(urlcc);
     http.addHeader("Content-Type", "application/x-binary");
    httpCode = http.GET();
     if (httpCode > 0) {
       if (httpCode == HTTP_CODE_OK) {
         http.writeToStream(&fdcc);
       }
     } else {
        debugLog("[HTTP] GET... failed, error: %s\n"); debugLogln(http.errorToString(httpCode).c_str());
     } 
     Serial.println("downloaded CC file");
     fdcc.close();
     http.end();
     Serial.print("df exit heap size:"); Serial.println(ESP.getFreeHeap());
}

/*
 * Delete all files in folders
 */

void deleteAll()
{
  File ls;
 
 
  

   
  deleteFolder("/cc/stories");
  deleteFolder("/nc/stories");


      
}

void deleteFolder(char *path)
{
  File nf;
  File dir;
   
  dir = SD.open(path);
  nf = dir.openNextFile();
  while (nf != NULL) {
      Serial.print(nf.name()); Serial.println(" deleted");
      SD.remove(nf.name());
      nf = dir.openNextFile();
  }
  dir.close();
  nf.close();
}

void sendData(char *p) {

  while (!(*p)) {
    Serial.print(p);
  }
}
void beep(int duration) 
{
  

    digitalWrite(BUZZER , HIGH);
  delay(duration/divider);        // ...for 1 sec
  digitalWrite(BUZZER , LOW);
  delay(duration/divider);        // ...for 1sec
}




/*
 * Code added for setting wifi password
 */

AsyncWebServer server(80);

const char* input_parameter1 = "input_ssid";
const char* input_parameter2 = "input_password";
const char *filename = "/etc/cfg";


// Variable to store the HTTP request
// Set web server port number to 80
const char index_html[] PROGMEM = R"rawliteral(
<!DOCTYPE HTML><html lang="en">

<head>
    <meta charset="UTF-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>
        html {
            font-family: Times New Roman;
            display: inline-block;
            text-align: center;
        }

        h3 {
            font-size: 3.0rem;
            color: #FF0000;
        }
    </style>
    <title>Configuration Page</title>
</head>

<body>
    <center>
        <h3>Welcome to TAG WiFi configuration</h3>
        <form action="/get">
            <table>
                <tr>
                    <td>Username:</td>
                    <td><input type="text" name="input_ssid" placeholder="Enter name Here"></td>
                </tr>
                <tr>
                    <td>Password:</td>
                    <td><input type="password" name="input_password" placeholder="Enter Password Here"></td>
                </tr>
                
            </table>
            <div class="text-center">
                <input type="submit" name="submit" value="Save">
            </div>
        </form>

    </center>
</body>

</html>)rawliteral";

const char success_html[] PROGMEM = R"rawliteral(
<!DOCTYPE HTML><html lang="en">

<head>
    <meta charset="UTF-8">
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>
        html {
            font-family: Times New Roman;
            display: inline-block;
            text-align: center;
        }

        h3 {
            font-size: 3.0rem;
            color: #FF0000;
        }
    </style>
    <title>Completed page</title>
</head>

<body>
    <center>
        <h3>Wifi id and password updated successfully! Press any key on Hexis to continue</h3>
    </center>
</body>

</html>)rawliteral";

void notFound(AsyncWebServerRequest *request) {
  request->send(404, "text/plain", "Not found");
}

void changePassword()
{
  APsetup();
  beep(200);
  delay(100);
  beep(200);
  delay(100);
  beep(200);
  server.on("/", HTTP_GET, [](AsyncWebServerRequest *request){
            request->send_P(200, "text/html", index_html);
          });
          
        
  server.on("/get", HTTP_GET, [] (AsyncWebServerRequest *request) {
    String input_id;
    String input_password;
    if (request->hasParam(input_parameter1)&& request->hasParam(input_parameter2)) {
      input_id = request->getParam(input_parameter1)->value();
      input_password = request->getParam(input_parameter2)->value();
      Serial.println("Entered ssid is: " + input_id);
      Serial.println("Entered password is: " + input_password);
      bool status = true;
      while(status){
        if (input_id == "" || input_password == ""){
          //request->send(200, "text/html", "ID and/or password missing.Enter again!");
          request->send(200, "text/html", "Username = " + input_id + "<br> password = " + input_password + "<br>Enter again!<br>" + "<br><a href=\"/\">Return to Home Page</a>");
          status = true;
        }
        else{
          status = false;
        }
      }
      update_ssid(input_id);
      update_pw(input_password);
      Serial.println(F("Printing config file contents..."));
      printFile(filename);
      request->send_P(200, "text/html", success_html);
      beep(200);
      delay(100);
      beep(200);
      delay(100);
      beep(200);
    }
  });
  server.onNotFound(notFound);
  server.begin();
}

void APsetup(){
  // Remove the password parameter, if you want the AP (Access Point) to be open
  WiFi.softAP("hexis", "");
  IPAddress IP = WiFi.softAPIP();
  Serial.print("Original AP IP address: ");
  Serial.println(IP);

  WiFi.mode(WIFI_AP);
  WiFi.softAP(ssid, password);
  Serial.println("Wait 100 ms for AP_START…");
  delay(100);

  Serial.println("Set softAPConfig");
  IPAddress Ip(192, 168, 1, 1);
  IPAddress NMask(255, 255, 255, 0);
  WiFi.softAPConfig(Ip, Ip, NMask);

  IPAddress myIP = WiFi.softAPIP();
  Serial.print("New AP IP address: ");
  Serial.println(myIP);
}


void update_ssid(String input_id){
  File file = SD.open(filename, FILE_WRITE);
  if (!file) {
    Serial.println(F("Failed to open file"));
    return;
  }
  // Set the values in the document
  cfgBuffer["wifiap"] = input_id;

  // Serialize JSON to file
  if (serializeJson(cfgBuffer, file) == 0) {
    Serial.println(F("Failed to write to file"));
  }
  file.close();
}
void update_pw(String input_password){
  File file = SD.open(filename, FILE_WRITE);
  if (!file) {
    Serial.println(F("Failed to open file"));
    return;
  }
  // Set the values in the document
  cfgBuffer["wifipw"] = input_password;

  // Serialize JSON to file
  if (serializeJson(cfgBuffer, file) == 0) {
    Serial.println(F("Failed to write to file"));
  }
  file.close();
}

void printFile(const char *filename) {
  // Open file for reading
  File file = SD.open(filename);
  if (!file) {
    Serial.println(F("Failed to read file"));
    return;
  }
 
  // Extract each characters by one by one
  while (file.available()) {
    Serial.print((char)file.read());
  }
  Serial.println();
 
  // Close the file
  file.close();
}
