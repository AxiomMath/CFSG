module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ThmR
public import CFSG.Quasithin.Vol2.Ch10SecC3A
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10

theorem ch10Reselect_holds
    : Ch10.Ch10Reselect :=
  have h37 : Vol2Native.A37ForSQTKCat := Vol2Native.a37ForSQTKCat_proved
  have h38 : Vol2Native.A38ForSQTKCat := SecA.a38ForSQTKCat_proved
  have h39 : Vol2Native.A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have h3228 : TmpL6_3_2_2_eight := stmt3_2_2_eight_proved
  ch10Reselect_of h37 h38 (tmpL6_3_2_2_two_of h3228 (stmt3_2_3_of h37 h38 h39))

end CFSG.Quasithin.Vol2.Ch10Reselect
