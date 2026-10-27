module

public import CFSG.Quasithin.Background.F918N9
public import CFSG.Quasithin.Background.F918U9
public import CFSG.Quasithin.Background.F918V6
public import CFSG.Quasithin.Background.F918S3
public import CFSG.Quasithin.Background.F918R4
public import CFSG.Quasithin.Background.F918XY
public import CFSG.Quasithin.Background.GoldschmidtD35Chk
public import CFSG.Quasithin.Background.GoldschmidtD35CoreMain
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin.H13

theorem d35InspUniq_holds : D35InspUniq :=
  d35InspUniq_of_chk (d35InspUniq8_of_core D35Core.d35ValCore_holds) D35Chk.run_eq_true

theorem d35_holds
    (hB51 : AsB51) (hB56 : AsB56) : D35 :=
  d35_of_inputs asB42_holds hB51 hB56 asA21SQTKSection asA36NoOddCover_holds
    (d35InspTwo_of_B51 hB51) d35InspSum_holds d35InspUniq_holds
    (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection))

theorem d35_proved :
    D35 :=
  d35_holds B5.asB51_holds asB56_holds

end CFSG.Quasithin.H13
