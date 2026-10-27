module

public import CFSG.Quasithin.Vol2.Ch10SecT701S
public import CFSG.Quasithin.Vol2.Ch10SecQ1Facts
public import CFSG.Quasithin.Vol2.Ch10SecC3A
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem323
public import CFSG.Quasithin.Background.F918K8
public import CFSG.Quasithin.Background.SmithB45Holds
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch10 CFSG.QuasithinUnique


theorem stmt7_0_1_shape_holds
    : Stmt7_0_1_shape := by
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := SecA.a38ForSQTKCat_proved
  have h39 := Vol2Native.a39ForSQTKCat_proved
  have h323 := stmt3_2_3_of h37 h38 h39
  exact SecA.stmt7_0_1_shape_of h37 h38 (tmpL6_3_2_2_two_of stmt3_2_2_eight_proved h323)
    asB45_holds SecA.facts10_1_holds insp5aNonShape_holds

end CFSG.Quasithin.H13
