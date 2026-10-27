module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NG
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316E
public import CFSG.Quasithin.Vol2.KGFact3312J1
public import CFSG.Quasithin.Vol2.KGFact3312J2
public import CFSG.Quasithin.Vol2.KGFact3312Lie2
public import CFSG.Quasithin.Vol2.KGFact3312L3
public import CFSG.Quasithin.Vol2.KGFactAutSylowM11
public import CFSG.Quasithin.Vol2.KGFactAutSylowM22
public import CFSG.Quasithin.Vol2.KGFactAutSylowM23
public import CFSG.Quasithin.Vol2.KGFactAutSylowJ4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

theorem L3312.facts3312_holds :
    L3312.Facts3312 where
  j1 := KG3312.factJ1Norm3312_holds
  j2 := KG3312.factJ2Norm3312_holds
  lie2 := KG3312.factLie2Norm3312_holds
  l3eps := KG3312.factL3EpsNorm3312_holds
  nonquasi := L3312.fact3312Nonquasi_holds
  l42 := KGAutSyl.factAutSylowL42_holds
  l52 := KGAutSyl.factAutSylowL52_holds
  a7 := KGAutSyl.factAutSylowA7_holds
  l2sq := KGAutSyl.factAutSylowL2Sq_holds
  l2four := KGAutSyl.factL2pSylowFour_holds
  l2outer := KGAutSyl.factAutL2pOuter_holds
  m11 := KGAutSyl.factAutSylowM11_holds
  m22 := KGAutSyl.factAutSylowM22_holds
  m23 := KGAutSyl.factAutSylowM23_holds
  m24 := KGAutSyl.factAutSylowM24_holds
  j4 := KGAutSyl.factAutSylowJ4_holds
  hs := KGAutSyl.factAutSylowHS_holds
  he := KGHe.factAutHeSylow_holds
  ru := KGAutSyl.factAutSylowRu_holds

theorem step3_3_12R_of_inputs
    (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h36 : Vol2Native.A36ForSQTKCat) (h128 : Lemma128One) :
    Step3_3_12R :=
  step3_3_12R_of h14 h37 h38 h39 h312 h36 h128 L3312.facts3312_holds

theorem step3_3_12RB_of_inputs
    (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h36 : Vol2Native.A36ForSQTKCat) (h128 : Lemma128One) :
    Step3_3_12RB :=
  step3_3_12RB_of h14 h37 h38 h39 h312 h36 h128 L3312.facts3312_holds

end CFSG.Quasithin.H13
