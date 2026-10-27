module

public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.AxisCount.BabySetup
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import Certificates.Certificate3027
public import CFSG.Monster.AxisCount.BabyCoverSpec

public section

namespace CFSG.Monster.Existence

theorem card_nativeB :
    Nat.card CFSG.Blueprint.NativeSporadic.B = CFSG.Open.monsterBabyOrder :=
  card_Cbar_eq_card_B.symm.trans AxisCount.Baby.natCard_Cbar_eq_monsterBabyOrder

end CFSG.Monster.Existence
