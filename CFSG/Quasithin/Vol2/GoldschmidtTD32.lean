module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328
public import CFSG.Quasithin.H13.VolII16
public import CFSG.Quasithin.Background.SmithB42Holds
public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

theorem stmt3_2_3_proved
    : Stmt3_2_3 :=
  stmt3_2_3_of Vol2Native.a37ForSQTKCat_proved C129Native.a38ForSQTKCat_proved
    Vol2Native.a39ForSQTKCat_proved

theorem stmt3_2_8_proved
    : Stmt3_2_8 :=
  stmt3_2_8_of asB42_holds VolI.asI16Cover328_holds

end CFSG.Quasithin.H13
