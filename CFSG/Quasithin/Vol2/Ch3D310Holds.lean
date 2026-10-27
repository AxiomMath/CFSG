module

public import CFSG.Quasithin.Background.SmithD310UHolds
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Background.F918WF
public import CFSG.Quasithin.Background.F918WG
public import CFSG.Quasithin.Background.F918WH
public import CFSG.Quasithin.Vol2.Ch3D310C0

public section

namespace CFSG.Quasithin.H13

namespace D310H

theorem d310C0_of (h : D310) : D310C0 :=
  fun W _ _ M Mp T L V hD hMp hq _ => h W M Mp T L V hD hMp hq

end D310H

theorem d310_holds
    : D310 :=
  d310_of_unfaithfulD d35_proved (d391Deep_of_inputs
      (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
          (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
          (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
          (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
      B5.asB51_holds asA21SQTKSection) d310Unfaith_holds

theorem d310C0_holds
    : D310C0 :=
  D310H.d310C0_of d310_holds

end CFSG.Quasithin.H13
