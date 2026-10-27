module

public import CFSG.Quasithin.Vol2.Ch11G2Q8NatFixed
public import CFSG.Quasithin.Vol2.Ch11SKFCompOrbit
public import CFSG.Quasithin.Vol2.Ch11SecB414W
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmY
public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4B
public import CFSG.Quasithin.Vol2.Ch11SecQ9aMain
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4L
public import CFSG.Quasithin.Vol2.Ch11SecWire11J
public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA4
public import CFSG.Monster.Schur.TripleM24
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_1_2StarW (h : PartsW) (h3_2_5 : H13.Stmt3_2_5) (h11_0_2 : Stmt11_0_2)
    (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0) (hTmpL6_4_2_13 : TmpL6_4_2_13) :
    SecA.Stmt11_1_2Star := by
  have hNatPointFacts : SecS.NatPointFacts := ⟨KGNat.factNatPointSL3_holds,
      SecS.factNatPointSp4_holds, G2Q8.factNatPointG2_holds⟩
  have hNatFixedFacts : SecS.NatFixedFacts := ⟨KGNat.factNatFixedSL3_holds,
      SecS.factNatFixedSp4_holds, G2Q8.factNatFixedG2_holds⟩
  have hObl11_1_2StarAmalgam := SecS.obl11_1_2StarAmalgam_of₃'' h.inputs.propF1_12L24 cartanFacts
      natFacts KGNat.factG2DerivedOrder_holds h11_0_2 h.proved.a3_7 h.proved.a3_8 h.proved.a3_9
  have hObl11_1_2StarShapeJ4 := SecS.obl11_1_2StarShapeJ4_of h.proved.factJ4UniqueL24 cartanFacts
      natFacts KGNat.factG2DerivedOrder_holds h11_0_2
  have hObl11_1_2StarShape := SecS.obl11_1_2StarShape_of SecS.factL34Parab_holds
      SecS.factL34Levi_holds SecS.factPGL34Torus_holds h.proved.factShapeInspect
      hObl11_1_2StarShapeJ4 cartanFacts natFacts KGNat.factG2DerivedOrder_holds h11_0_2
      h.proved.factL2Parabolic h.proved.a3_6 h.proved.a312ForSQTK
  have hObl11_1_2StarSL3 := SecS.obl11_1_2StarSL3_of_facts₂ hTmpL6_4_2_13 h.proved.factNot4213
      h.inputs.in10.thm3_3_1 h.proved.as_A_1_28 hObl11_1_2StarAmalgam hObl11_1_2StarShape
      h.proved.factShapeWeyl SecS.factL34Parab_holds SecS.factL34Levi_holds
      SecS.factPGL34Torus_holds SecS.factL34NoE9_holds h.proved.a3_7 h.proved.a3_8 h.proved.a3_9
      SecS.KF.factCompOrbit_holds h.proved.factSchreierComp h.sec1.factJ4Inspect
      (SecS.J4Mult.factJ4Multiplier_of_noTripleCover
          CFSG.Monster.Schur.noPerfectTripleCover_nativeM24) cartanFacts natFacts KGNat.factG2DerivedOrder_holds
      h.proved.facts12b
      h11_0_2 h11_0_3
  have hStmt3_2_8 := h.proved.lem3_2_8
  exact SecS.stmt11_1_2Star_of4 SecS.factL34Parab_holds SecS.factPGL34Levi_holds
      SecS.factL34Levi_holds SecS.factPGL34Torus_holds h.proved.factShapeInspect
      SecS.factL34NoE9_holds h.proved.factParabGen h.proved.factBorelShape h.proved.factParabTwo
      hNatPointFacts hNatFixedFacts cartanFacts natFacts KGNat.factG2DerivedOrder_holds
      h.proved.factG2AdjointOrder h.proved.rankTwoQuasisimple h.proved.factL2Parabolic
      h.proved.facts02 h.proved.factList3Table h.proved.facts12 h.proved.facts11 h11_0_2 h11_1_0
      h.proved.lemma128Four h.proved.lem1_2_8_one h.proved.stmtFSUChoice (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1)
      h3_2_5 hStmt3_2_8 h.proved.lem3_2_2_eight h.proved.a318Facts h.proved.a3_6 h.proved.a3_7
      h.proved.a3_8 h.proved.a3_9 h.proved.a312ForSQTK hObl11_1_2StarAmalgam hObl11_1_2StarShapeJ4
      hObl11_1_2StarSL3

end CFSG.Quasithin.Vol2.Ch11.Wire11
