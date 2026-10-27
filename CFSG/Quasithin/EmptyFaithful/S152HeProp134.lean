module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9Native
public import CFSG.Quasithin.Background.C129NativeLight
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts134E9Proof
public import CFSG.Quasithin.Vol2.GoldschmidtF134J4
public import CFSG.Quasithin.Vol2.F134LieU3
public import CFSG.Quasithin.Vol2.F134LieL3
public import CFSG.Quasithin.Vol2.F134LieSp4
public import CFSG.Quasithin.Vol2.F134LieF4
public import CFSG.Quasithin.Vol2.F134LieD4
public import CFSG.Quasithin.Vol2.F134LieG2
public import CFSG.Quasithin.Vol2.F134LieOdd

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

theorem prop134E9He_holds :
    EmptyFaithfulMultiple.Prop134E9He :=
  P134.prop134E9He_of_facts Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved
    C129Native.a38ForSQTKCat_proved
    (P134.facts134E9He_of_rest_of_he ({ toFacts134E9Lie := { psl3Plus := P134.facts134E9_psl3Plus,
                                                             psu3Minus := P134.facts134E9_psu3Minus,
                                                             psl3Even := P134.facts134E9_psl3Even,
                                                             psu3Even := P134.facts134E9_psu3Even,
                                                             psp4Even := P134.facts134E9_psp4Even,
                                                             g2Even := P134.facts134E9_g2Even,
                                                             d4Even := P134.facts134E9_d4Even,
                                                             f4Even := P134.facts134E9_f4Even },
                                        j4 := P134.facts134E9_j4 })
      P134.facts134E9_he)

end CFSG.Quasithin
