module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aRole
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B
public import CFSG.Quasithin.Vol2.Ch11SecSZK9

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecA

theorem stmt11_1_2Star_of4
    (hF : FactL34Parab) (hPGL : FactPGL34Levi) (hLevi : FactL34Levi)
    (hT : FactPGL34Torus) (hIns : FactShapeInspect) (hNo : FactL34NoE9) (hPG : FactParabGen)
    (hB : FactBorelShape) (hPT : FactParabTwo) (hNP : NatPointFacts) (hNF : NatFixedFacts)
    (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder) (hG2a : FactG2AdjointOrder)
    (hRQ : RankTwoQuasisimple) (hFp : FactL2Parabolic) (hF02 : Facts02) (hL3 : FactList3Table)
    (hF12 : Facts12) (hF11 : Facts11) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h128 : Lemma128Four) (h1281 : Lemma128One) (hfsu : Ch10.StmtFSUChoice)
    (h701 : Stmt7_0_1) (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) (h8 : Ch10.TmpL6_3_2_2_eight)
    (h318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (hAm : Obl11_1_2StarAmalgam)
    (hJ4 : Obl11_1_2StarShapeJ4) (hSL3 : Obl11_1_2StarSL3) : Stmt11_1_2Star :=
  stmt11_1_2Star_of''' hF hPGL hLevi hT hIns hNo hPG hB hPT hNP hNF hC hN hG2 hG2a hRQ hFp h1102
    h1110 h128 hfsu h36 h37 h38 h39 h312 hAm hJ4 hSL3
    (obl11_1_2StarZK_of factL34NotL42_holds hF02 h1281 h37 h312 hfsu h701 h325 h328 h8
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
      (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num))
    (obl11_1_2StarSymRole'_of factL34NotL42_holds hL3 hF12 hC hF11 hN h1102 h318 h36 h37 h38
      h39 h312)

end CFSG.Quasithin.Vol2.Ch11.SecS
