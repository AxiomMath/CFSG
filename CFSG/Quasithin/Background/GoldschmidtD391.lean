module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.Background.F918N9
public import CFSG.Quasithin.Background.F918R4
public import CFSG.Quasithin.Background.F918S3
public import CFSG.Quasithin.Background.F918U9
public import CFSG.Quasithin.Background.F918WF
public import CFSG.Quasithin.Background.F918WG
public import CFSG.Quasithin.Background.F918WH
public import CFSG.Quasithin.Background.F918XY
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51

public section

namespace CFSG.Quasithin

theorem d391_holds :
    D391 :=
  d391L_of_deep (d391Deep_of_inputs
      (d35_of_inputs asB42_holds B5.asB51_holds asB56_holds asA21SQTKSection asA36NoOddCover_holds
          (d35InspTwo_of_B51 B5.asB51_holds) d35InspSum_holds
          (d35InspUniq_of_chk (d35InspUniq8_of_chk d35ValChk_run) d35Chk_run)
          (d35InspB42_of_orbit asA21SQTKSection (F918X.d35InspOrbit_proved asA21SQTKSection)))
      B5.asB51_holds asA21SQTKSection)

end CFSG.Quasithin
