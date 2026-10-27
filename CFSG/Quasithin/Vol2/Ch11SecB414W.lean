module

public import CFSG.Quasithin.Vol2.Ch11SecB414Z
public import CFSG.Quasithin.Vol2.Ch11SecS12ZR

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem obl11_1_2StarSL3_of_facts₂ (h4213 : TmpL6_4_2_13)
    (hNot4213 : SecB.FactNot4213) (h331 : Stmt3_3_1) (h128 : ASInputs.AS_A_1_28)
    (hAm : Obl11_1_2StarAmalgam) (hSh : Obl11_1_2StarShape) (hW : FactShapeWeyl)
    (hF : FactL34Parab) (hLevi : FactL34Levi) (hT : FactPGL34Torus) (hNo : FactL34NoE9)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hOrb : FactCompOrbit)
    (hSch : FactSchreierComp) (hJ4 : FactJ4Inspect)
    (hJ4M : FactJ4Multiplier) (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) : Obl11_1_2StarSL3 :=
  obl11_1_2StarSL3_of_core H13.Ch4.B414.lemmaB414Corrected_holds
      (obl11_1_2StarSL3AbCore_of h4213 hNot4213 h331 h128 hAm hSh hW hF hLevi hT hNo h37 h38 h39
          hOrb hSch hJ4 hJ4M hC hN hG2 hFb h1102) hC hN hG2 hFb h1102 h1103

end CFSG.Quasithin.Vol2.Ch11.SecS

