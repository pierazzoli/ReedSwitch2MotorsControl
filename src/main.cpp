
/* -------------------------------------------------------------------------------
    __________                          .___     .__
   \______   \ ____   ____ _____     __| _/____ |__|___________
     |       _//  _ \_/ ___\\__  \   / __ |/ __ \|  \_  __ \__  \
     |    |   (  <_> )  \___ / __ \_/ /_/ \  ___/|  ||  | \// __ \_
     |____|___/\____/ \_  __>______/\_____|\____ >__||__|  (______/
                        \/
                  _________                      __
                /   _____/ _____ _____ ________/  |_
                \_____  \ /     \\__  \\_  __ \   __\
                /        \  Y Y  \/ __ \|  | \/|  |
               /________ /__|_|__(______/__|   |__|
  -------------------------------------------------------------------------------
    Sistema de Controle da Vazão por velocidade para Roçadeiras Químicas
    Com Reed Switchs


    Version: 1.1
    Date: 31/01/2022
    Autor: Eugênio Pierazzoli
    pierazzoli@gmail.com
    eugenio.pierazzoli@aluno.unipampa.edu.br

    Mestrado PPGCAP: 2020-2022
    PPGCAP (Programa de Pós-graduação em Computação Aplicada)
    Unipampa Campus Bagé e Embrapa Pecuária Sul

    Grupo de Pesquisa / Mestrado
    Orientador:     Dr. Naylor Bastiani Perez     (Embrapa  - Pecuária Sul)
    Coorientador:   Dr. Leonardo Bidese de Pinho  (Unipampa - Campus Bagé)
    Iniciação Científica (Engecomp): Willian Domingues (Unipampa - Campus Bagé)

  -------------------------------------------------------------------------------

*/

// ==============================================================================
// ------------------------ Dependencies  ------------------------
// ==============================================================================

#include <Arduino.h>
#include <math.h>
#include <Wire.h>
//#include <LiquidCrystal_I2C.h> // * YWROBOT Library version:1.1
#define cPI 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899

#include<Time.h>               // * Paul Stoffregen Library version:1.6.1
#include<TimeAlarms.h>

//#include <EEPROM.h>


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
#define DEBUGMODE  // comment out to enable debug mode and display additional information about the serial port
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  PINs, constants and variables
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define mLperCicle 25.0                 // 25 to 27 ml per bomb cicle
double litersPerHectare = 32.0;         // A default value for 50% infestation is 32 L/ha

float sector_size = 3.6;
float sectors = 2;

#define VGS_MIN 2.0                     // Mosfet IRF1404 voltages pwm--> 102.4 for 2v
#define VGS_MAX 4.0                     // Mosfet IRF1404 voltages pwm--> 204.8 for 4v

//https://html.alldatasheet.com/html-pdf/834116/ISC/IRF1404/114/2/IRF1404.html

#define VGS_MIN_PWM VGS_MIN * 256.0/5.0 //Mosfet IRF1404 (Duty ÷ 256) x 5 V.
#define VGS_MAX_PWM VGS_MAX * 256.0/5.0 //Mosfet IRF1404 (Duty ÷ 256) x 5 V.

#define pwmStep 5                       // Steps for value change

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Clock Constants and variables
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// initial time display
volatile int hr  = 9;
volatile int min = 56;
volatile int sec = 45;
// initial date display
volatile int iday   = 1;
volatile int imonth =  2;
volatile int iyr    = 21;


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Reed Switchs
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define debouceTime 35                                // Reed Switch debounce ms

#define REED_SWITCH_1_PIN 4                           // Reed Switch 1 Pin
#define REED_SWITCH_2_PIN 5                           // Reed Switch 2 Pin
#define REED_SWITCH_3_PIN 6                           // Reed Switch 3 Pin

static uint32_t RTCLastTimeButton ,  RTCnow = 0;
//static uint32_t RTCLastTime ,  RTCrefreshSpeeds = 0;


volatile unsigned long timeFirstPulseRS_1 = 0;
volatile unsigned long timeFirstPulseRS_2 = 0;
volatile unsigned long timeFirstPulseRS_3 = 0;

volatile unsigned long timeLastPulseRS_1 = 0;
volatile unsigned long timeLastPulseRS_2 = 0;
volatile unsigned long timeLastPulseRS_3 = 0;

volatile unsigned long pulsesRS_1 = 0;
volatile unsigned long pulsesRS_2 = 0;
volatile unsigned long pulsesRS_3 = 0;

#define magnetsRS_1   3                          // Magnets in the system
#define magnetsRS_2   3                          // Magnets in the system
#define magnetsRS_3   3                          // Magnets in the system



/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Wheel Constants
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

const double wheelRadius = 0.28702;             // Radius of the wheel in m. Campo Limpo (car tire 175 70 r13) =  22,6" diameter
// https://tire-calc.com/pt/comparison/175-70-r13-and-175-70-r13-inch/
//const double wheelRadius = 0.337;             // Radius of the wheel in m. for bicycle  26" 2.1

#define  WHEEL_DIAMETER (wheelRadius * 2.0)     // Diameter of the wheel in m.
float d = (2 * wheelRadius*cPI) / magnetsRS_1;  // Calculation of the distance between two magnet transitions is done automatically.

float distance_sum = 0;
float distanceKM_sum = 0;

int val_N = HIGH;                              // NEW value of sensor
int val_P = HIGH;                              // PREDECESSOR value of sensor
long counter = 100000;                         // approx.  23s
unsigned long transitions = 0;                 // 0 to 4,294,967,295 (2^32 - 1).

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Menu Buttons, display and adjusts
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define BUTTON_1_PIN  8                                    //GPIO Pin 8 - button 1 - pullup Input
#define BUTTON_2_PIN  9                                    //GPIO Pin 9 - button 2 - pullup Input

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

////////////////////////
//  M1 PARAMETERS
#define MOTOR_1_PIN   10                                   // Motor 1 - Analog PWM PIN - value from 0 to 255

////////////////////////
//   M2 PARAMETERS
#define MOTOR_2_PIN   11                                   // Motor 2 - Analog PWM PIN - value from 0 to 255

#define odoMode 0 // km/h

volatile double speedNow = 0;
volatile double averangeSpeed = 0;
volatile double maxSpeed = 0;
volatile unsigned long distance = 0;
volatile unsigned long distanceKm = 0;
volatile unsigned long aplicationTime = 0;
volatile unsigned long totalTime = 1;

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//   FUNCTIONS
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void dosageAdjust (int step);

double calcCadence (unsigned long timeFirstPulse, unsigned long timeLastPulse, unsigned int pulses, unsigned int magnets );
double calcSpeed (double cadence );
double calcRPM (double litersPerHectare , double sector_size, double speed  );

void hamsterMode (void);
void update_serial (void);

void rsPulse1 (void);
void rsPulse2 (void);
void rsPulse3 (void);

int  getvalRS1 (void);
int  getvalRS2 (void);
int  getvalRS3 (void);

void printDigits(int digits);
void digitalClockDisplay (void);

void debugTesteINs (void);

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
void setup () {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  Serial.begin(9600);

#if defined DEBUGMODE
  // open serial monitor
  Serial.print("booting...");
  delay(100);                                             // The opening of the serial monitor takes some time
#endif

  pinMode(REED_SWITCH_1_PIN, INPUT);                      // Set pin as INPUT                    
  pinMode(REED_SWITCH_2_PIN, INPUT);                      // Set pin as INPUT
  pinMode(REED_SWITCH_3_PIN, INPUT);                      // Set pin as INPUT

  pinMode(BUTTON_1_PIN, INPUT_PULLUP);                    // Set the button as INPUT_PULLUP
  pinMode(BUTTON_2_PIN, INPUT_PULLUP);                    // Set the button as INPUT_PULLUP

  pinMode(MOTOR_1_PIN, OUTPUT);                           // Set output for motor 1
  analogWrite (MOTOR_1_PIN , 0);

  pinMode(MOTOR_2_PIN, OUTPUT);                           // Set output for motor 2
  analogWrite (MOTOR_2_PIN , 0);


#if defined DEBUGMODE
  while (!Serial); // Serial Debug Menu
  Serial.println(" ... OK");
#endif

 setTime(hr, min , sec, iday, imonth, iyr);

}

void loop() {

  RTCnow = millis();

#if defined DEBUGMODE
  // debugTesteINs ();
#endif //DEBUGMODE

  if (getvalRS1()) rsPulse1 ();
  if (getvalRS2()) rsPulse2 ();
  if (getvalRS3()) rsPulse3 ();


  double cadence1 = calcCadence (timeFirstPulseRS_1, timeLastPulseRS_1, pulsesRS_1, magnetsRS_1);
  double cadence2 = calcCadence (timeFirstPulseRS_2, timeLastPulseRS_2, pulsesRS_2, magnetsRS_2);
  double cadence3 = calcCadence (timeFirstPulseRS_3, timeLastPulseRS_3, pulsesRS_3, magnetsRS_3);

  speedNow = calcSpeed(cadence1);
  averangeSpeed = distance / totalTime;
  if (speedNow > maxSpeed ) maxSpeed = speedNow;

  Serial.print ("cadence1: ");
  Serial.println (cadence1);
  Serial.print ("cadence2: ");
  Serial.println (cadence2);
  Serial.print ("cadence3: ");
  Serial.println (cadence3);

  hamsterMode();
  dosageAdjust (0.5);


}//end loop


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  SUBROUTINES
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

double calcCadence(unsigned long timeFirstPulse, unsigned long timeLastPulse, unsigned int pulses, unsigned int magnets ) {  // Calculate cadence in rpm
  double cadence = 0.0;

  //cadence = (( pulses * 1000.0) / ((millis() - timeCadence) * 4) * 60);
  cadence = ((pulses * 60000.0 / (timeLastPulse - timeFirstPulse)) / magnets );
  // timeFirstPulse = 0;
  // pulses = 0;

  return cadence; //RPM
}


double calcSpeed(double cadence ) {
  double speed = 0.0;

  //Speed (meters per minute)  =   pi x Wheel Diameter (meters) x cadence (RPM)

  //Speed (km/h)  =  pi x Wheel Diameter (meters) x cadence (RPM)  x 0.0600000000000 (60min/10000m)
  //Speed (mph)  =   pi x Wheel Diameter (meters) x cadence (RPM)  x 0.0372822715344 (0,00062137119224*60 min)
  //Speed (m/s)  =   pi x Wheel Diameter (meters) x cadence (RPM)  x 0.0166666666667 (1s/60min)

  //1m / 1609.344 = 0.00062137119224mi

  //speed = ((cPI * WHEEL_DIAMETER * hallpulses * 1000.0) / ((millis() - timeSpeed) * 4) * 3.6);  // Calculate speed in Km/h
  if (odoMode == 0)
  {
    speed = (cPI * WHEEL_DIAMETER * cadence * 0.06) ; // Km/h
  }

  else if  (odoMode == 1)
  {
    speed = (cPI * WHEEL_DIAMETER * cadence * 0.0372822715); // Mph
  }
  else // if  (odoMode == 2 )
    //speed = ((cPI * WHEEL_DIAMETER * hallpulses * 1000.0) / ((millis() - timeSpeed) * 4))
  {
    speed = (cPI * WHEEL_DIAMETER * cadence / 60.0) ; // m/s
  }

  return speed;
}

//for interruption
void rsPulse1 () {
  unsigned long now = millis();
  if (now - timeLastPulseRS_1 > debouceTime) {                  // debouce input for hall or reed switch
    pulsesRS_1 ++;
    timeLastPulseRS_1 = now;
    // if (timeFirstPulseRS_1 == 0)  timeFirstPulseRS_1 = now;
#if defined DEBUGMODE
    Serial.println("rsPulse1");
#endif
  }
}

//for interruption
void rsPulse2 () {
  unsigned long now = millis();
  if (now - timeLastPulseRS_2 > debouceTime) {                  // debouce input for hall or reed switch
    pulsesRS_2 ++;
    timeLastPulseRS_2 = now;
    // if (timeFirstPulseRS_2 == 0)  timeFirstPulseRS_2 = now;

#if defined DEBUGMODE
    Serial.println("rsPulse2");
#endif
  }
}

//for interruption
void rsPulse3 () {
  unsigned long now = millis();
  if (now - timeLastPulseRS_3 > debouceTime) {                  // debouce input for sensor hall or reed switch
    pulsesRS_3 ++;
    timeLastPulseRS_3 = now;
    // if (timeFirstPulseRS_3 == 0)  timeFirstPulseRS_3 = now;

#if defined DEBUGMODE
    Serial.println("rsPulse3");
#endif
  }
}


void debugTesteINs () {

  int rs1State = digitalRead(REED_SWITCH_1_PIN);      // Reading pin value
  int rs2State = digitalRead(REED_SWITCH_2_PIN);      // Reading pin value
  int rs3State = digitalRead(REED_SWITCH_3_PIN);      // Reading pin value

  int button1State = digitalRead(BUTTON_1_PIN);       // Reading pin value
  int button2State = digitalRead(BUTTON_2_PIN);       // Reading pin value

  if (rs1State == LOW) {
    Serial.println("RS1");
  }

  if (rs2State == LOW) {
    Serial.println("RS2");
  }

  if (rs3State == LOW) {
    Serial.println("RS3");
  }

  if (button1State == 0) {
    Serial.println("B1");
  }

  if (button2State == 0) {
    Serial.println("B2");
  }
  delay(100);
}

void hamsterMode() {
  //evaluate sensor
  val_N = getvalRS1();
  // Check the values PREVIOUS (val_P) and NEW (val_N)
  // If val_P == HIGH and val_N == LOW, the magnet gets under the sensor: the sensor LED is on.

  if (val_P == HIGH && val_N == LOW)
  {
    // magnet under sensor
    // delay (10);
    // Update TOGGLE variables
    val_P = val_N;
   
  } else if (val_P == LOW && val_N == HIGH) {
    // If val_P == LOW and val_N == HIGH, it means that the sensor has passed, so the counter must go on by one
    transitions++;

#if defined DEBUGMODE
    update_serial();
#endif

    //align states
    val_P = val_N;
  } 
}


int  getvalRS1() {
  int sensor1 = digitalRead (REED_SWITCH_1_PIN);
  return sensor1;
}

int  getvalRS2() {
  int sensor2 = digitalRead (REED_SWITCH_2_PIN);
  return sensor2;
}

int  getvalRS3() {
  int sensor3 = digitalRead (REED_SWITCH_3_PIN);
  return sensor3;
}

void  update_serial() {
  Serial.print ("Pulses: ");
  Serial.print(transitions);

  Serial.print ("\t Distance: ");
  distance_sum = transitions * d;
  Serial.print(distance_sum);
  // Update TOGGLE variables
  Serial.println("m");
}

double calcRPM ( double litersPerHectare , double sector_size, double speed  ) {
  double rpm = (litersPerHectare * sector_size * speed * 1.6667) / mLperCicle;
  return (rpm);
}




void digitalClockDisplay()
{
  Serial.print(hour());
  printDigits(minute());
  printDigits(second());
  Serial.println();
}

void printDigits(int digits)
{
  Serial.print(":");
  if (digits < 10)
    Serial.print('0');
  Serial.print(digits);
}


/*!
  @function
  @abstract   Increment ou decrement dosage
  @discussion  Use add ir sub L/ha buttons.
 @param      step[in] add or sub a value
*/
void dosageAdjust (int step) {
  while ((RTCnow - RTCLastTimeButton) > 1000 ) // wait1000ms
  {
    volatile boolean button1;
    volatile boolean button2;

    /*------- Dosage Set -------*/
    button1 = digitalRead(BUTTON_1_PIN);
    if (button1 == 0)
    {
      litersPerHectare = litersPerHectare + step;
    }

    button2 = digitalRead(BUTTON_1_PIN);
    if (button2 == 0)
    {
      litersPerHectare = litersPerHectare - step;
      if (litersPerHectare < 0) litersPerHectare = 0; // Not negative
    }

    RTCLastTimeButton = RTCnow;
    
#if defined DEBUGMODE
    Serial.print("Liters per hectare: ");
    Serial.println(litersPerHectare);
#endif
  }
}
