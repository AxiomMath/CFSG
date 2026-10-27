module

public import CFSG.Quasithin.Background.F918XZ
public import CFSG.Quasithin.Background.F918XN1
public import CFSG.Quasithin.Background.F918XN2
public import CFSG.Quasithin.Background.F918XN3
public import CFSG.Quasithin.Background.F918XAL1
public import CFSG.Quasithin.Background.F918XAL2Six
public import CFSG.Quasithin.Background.F918XAL2Seven
public import CFSG.Quasithin.Background.F918XE1
public import CFSG.Quasithin.Background.F918XG2a
public import CFSG.Quasithin.Background.F918XG2b
public import CFSG.Quasithin.Background.F918XV8aMain
public import CFSG.Quasithin.Background.F918XV8b

public section

namespace CFSG.Quasithin.F918X


theorem d35InspOrbit_proved (hA21 : AsA21SQTKSection) : D35InspOrbit :=
  d35InspOrbit_of_cases hA21 noOddCoverHatA6_holds case1Twist_holds case2Twist_holds
    case3TwistOne_holds case3TwistBig_holds case4TwistOne_holds case4TwistBig_holds
    case5Twist_holds case6Twist_holds case7Twist_holds case8Twist_holds case9Twist_holds
    case10Twist_holds case11Twist_holds

end CFSG.Quasithin.F918X
