module

public import CFSG.Quasithin.Vol2.Ch11SecWire11L
public import CFSG.Quasithin.Vol2.Ch11SecA15MainW
public import CFSG.Quasithin.Vol2.Ch11G2Q8Offender
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffenderRad
public import CFSG.Quasithin.Vol2.Ch11G2Q8Repair
public import CFSG.Quasithin.Vol2.Ch11G2Q8RootLineRad
public import CFSG.Quasithin.Vol2.Ch11G2Q8TwelveRad
public import CFSG.Quasithin.Vol2.Ch11SecA13Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Main
public import CFSG.Quasithin.Vol2.Ch11SecAKA13
public import CFSG.Quasithin.Vol2.Ch11SecAKA4
public import CFSG.Quasithin.Vol2.Ch11SecAKA9
public import CFSG.Quasithin.Vol2.Ch11SecAKB4
public import CFSG.Quasithin.Vol2.Ch11SecAKC6
public import CFSG.Quasithin.Vol2.Ch11SecB21Main
public import CFSG.Quasithin.Vol2.Ch11SecB22Main
public import CFSG.Quasithin.Vol2.Ch11SecB23Main
public import CFSG.Quasithin.Vol2.Ch11SecB24Main
public import CFSG.Quasithin.Vol2.Ch11SecB25
public import CFSG.Quasithin.Vol2.Ch11SecB33
public import CFSG.Quasithin.Vol2.Ch11SecB34
public import CFSG.Quasithin.Vol2.Ch11SecBG2Done
public import CFSG.Quasithin.Vol2.Ch11SecBK2C
public import CFSG.Quasithin.Vol2.Ch11SecBK2F
public import CFSG.Quasithin.Vol2.Ch11SecBK4J
public import CFSG.Quasithin.Vol2.Ch11SecBK4O
public import CFSG.Quasithin.Vol2.Ch11SecBK5A
public import CFSG.Quasithin.Vol2.Ch11SecBK5B
public import CFSG.Quasithin.Vol2.Ch11SecBK6E
public import CFSG.Quasithin.Vol2.Ch11SecBK6N
public import CFSG.Quasithin.Vol2.Ch11SecBK7J
public import CFSG.Quasithin.Vol2.Ch11SecBK7L
public import CFSG.Quasithin.Vol2.Ch11SecBK7S
public import CFSG.Quasithin.Vol2.Ch11SecBK9T
public import CFSG.Quasithin.Vol2.Ch11SecE3PerH
public import CFSG.Quasithin.Vol2.Ch11SecOE3A
public import CFSG.Quasithin.Vol2.Ch11SecQ9bMain
public import CFSG.Quasithin.Vol2.Ch11SecQ9bRadUU5
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW
public import CFSG.Quasithin.Vol2.Ch11SecWire11J

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_1_2W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_1 : Stmt11_1_1)
    (h11_1_2Star : SecA.Stmt11_1_2Star) : Stmt11_1_2 :=
  SecA.stmt11_1_2_of h.proved.facts12 h.proved.facts12b h.proved.facts12c cartanFacts
    h.proved.facts11 natFacts KGNat.factLineSp4_holds SecA.factLineG2_holds h.proved.factParabGen
    h.proved.a318Facts h.proved.a3_6 h.proved.a3_8 h.proved.a3_6CoreCat h.proved.tmp1_3_3
    h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_1_1 h11_1_2Star

theorem stmt11_1_3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_2 : Stmt11_1_2)
    : Stmt11_1_3 :=
  SecA.stmt11_1_3_of h.proved.a3_7Cat natFacts KGNat.factG2DerivedOrder_holds h.inputs.in10.thm3_3_1
    h11_0_2 h11_0_3 h11_1_2 KGNat.factLineSL3_holds KGNat.factLineSp4_holds SecA.factLineG2_holds

theorem stmt11_1_4W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0) (h11_1_3 : Stmt11_1_3)
    : Stmt11_1_4 :=
  SecA.stmt11_1_4_of h.inputs.in10.thm3_3_1 natFacts h11_0_2 h11_1_0 h11_1_3
    KGNat.factDeltaSp4_holds SecA.factDeltaG2_holds

theorem stmt11_1_2RadUW (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3)
    (h11_1_1 : Stmt11_1_1) : SecA.C11P9B.Stmt11_1_2RadU :=
  SecA.C11P9B.stmt11_1_2RadU_of h.proved.facts12 h.proved.facts12b h.proved.facts12c cartanFacts
    h.proved.facts11 natFacts KGNat.factLineSp4_holds SecA.factLineG2_holds h.proved.factParabGen
    h.proved.a318Facts h.proved.a3_6 h.proved.a3_7 h.proved.a3_8 h.proved.a3_9 h.proved.a312ForSQTK
    h.proved.a3_6CoreCat h.proved.tmp1_3_3 h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_1_1

theorem stmt11_2_2W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3)
    (hTmpL6_4_2_13 : TmpL6_4_2_13) (h11_0_4 : Stmt11_0_4) (h11_1_3 : Stmt11_1_3)
    (h11_1_4 : Stmt11_1_4) (h11_1_2RadU : SecA.C11P9B.Stmt11_1_2RadU) : Stmt11_2_2 := by
  have hRad11_1_3 := G2Q8.rad11_1_3_of h.proved.a3_7Cat KGNat.factG2DerivedOrder_holds h11_0_2
      KGNat.factLineSL3_holds KGNat.factLineSp4_holds SecA.factLineG2_holds G2Q8.factSiegelG2_holds
      h11_1_2RadU
  have hDerivedG2WeakClosureRad := G2Q8.derivedG2WeakClosureRad_of G2Q8.factG2OffenderRad_holds
      G2Q8.factG2RootLineRad_holds G2Q8.factG2LineGen_holds natFacts SecB.factMParam_holds
      SecB.factOddCodim_holds SecB.factHyperplaneT_holds SecB.factSp4FourExt_holds
      h.proved.factNot4213 SecB.factRootInv_holds KGNat.factG2DerivedOrder_holds hTmpL6_4_2_13
      h.proved.theorem311Stmt h.inputs.in10.thmE6_3 h.proved.as_E_6_12 h.proved.lemE6_6_four
      h.proved.as_E_6_14 h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_0_4 h11_1_4 hRad11_1_3
  have hFactsG2W : SecB.FactsG2W := ⟨G2Q8.factG2Offender_holds, G2Q8.factG2RootLine_holds,
      G2Q8.factG2LineGen_holds⟩
  have hDerivedG2WeakClosure := SecB.derivedG2WeakClosure_of_parts hDerivedG2WeakClosureRad
      hFactsG2W natFacts SecB.factMParam_holds SecB.factOddCodim_holds SecB.factHyperplaneT_holds
      SecB.factSp4FourExt_holds h.proved.factNot4213 SecB.factRootInv_holds
      KGNat.factG2DerivedOrder_holds hTmpL6_4_2_13 h.proved.theorem311Stmt h.inputs.in10.thmE6_3
      h.proved.as_E_6_12 h.proved.lemE6_6_four h.proved.as_E_6_14 h.inputs.in10.thm3_3_1 h11_0_2
      h11_0_3 h11_0_4 h11_1_3 h11_1_4
  exact SecB.stmt11_2_2_of natFacts SecB.factMParam_holds SecB.factOddCodim_holds
      SecB.factHyperplaneT_holds SecB.factSp4FourExt_holds h.proved.factNot4213
      SecB.factRootInv_holds SecB.factA2InL_holds SecB.factFlagOneCentral_holds
      G2Q8.factG2Twelve_holds hDerivedG2WeakClosure hTmpL6_4_2_13 h.proved.theorem311Stmt
      h.inputs.in10.thmE6_3 h.proved.as_E_6_12 h.proved.lemE6_6_four h.proved.as_E_6_14
      h.proved.lem3_2_2_eight h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_0_4 h11_1_4

theorem stmt11_2_4W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_3 : Stmt11_1_3)
    (h11_2_2 : Stmt11_2_2) : Stmt11_2_4 :=
  SecB.stmt11_2_4_of SecB.factRootPoint_holds SecB.factPointTrans_holds SecB.factR2_holds
    SecB.factR2Line_holds SecB.factR2Gen_holds SecB.factL2Point_holds SecB.factSp4Root_holds
    SecB.factSp4NoTransv_holds natFacts h.inputs.in10.thm3_3_1 h.proved.lem3_2_2_eight h11_0_2
    h11_0_3 h11_1_3 h11_2_2

theorem stmt11_2_5W (h : PartsW) (h11_2_4 : Stmt11_2_4) : Stmt11_2_5 :=
  SecB.stmt11_2_5_of h.inputs.in10.thm3_3_1 h.proved.lem3_2_2_eight h11_2_4

theorem stmt11_1_5W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (hTmpL6_4_2_13 : TmpL6_4_2_13) (h11_0_4 : Stmt11_0_4) : Stmt11_1_5 := by
  have hFacts15c : SecA.Facts15c := ⟨KGNat.factRadicalInnerSL3_holds,
      KGNat.factRadicalInnerSp4_holds, KGNat.factPointTorusSL3_holds, KGNat.factPointTorusSp4_holds,
      KGNat.factRadicalCocycleSp4_holds⟩
  exact SecA.stmt11_1_5_ofW h.inputs.in10.thm3_3_1 h.inputs.thmC1_32 h.inputs.thmC1_34 hTmpL6_4_2_13
      h.proved.facts15 hFacts15c h.proved.facts11 natFacts KGNat.factG2DerivedOrder_holds h11_0_2
      h11_0_3 h11_0_4 h11_1_0

theorem stmt11_2_3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0) (h11_1_2 : Stmt11_1_2)
    (h11_1_5 : Stmt11_1_5) : Stmt11_2_3 :=
  SecB.stmt11_2_3_of pointFacts natFacts h.proved.as_A_1_12 h.inputs.in10.thm3_3_1 h11_0_2 h11_1_0
    h11_1_2 h11_1_5

theorem stmt11_3_3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_2_2 : Stmt11_2_2)
    (h11_2_5 : Stmt11_2_5) (h11_2_3 : Stmt11_2_3) : Stmt11_3_3 :=
  SecB.stmt11_3_3_of natFacts h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_2_2 h11_2_3 h11_2_5

theorem e114ForE22RW (h : PartsW) (hE114OneRes : E2.E22N.E114OneRes) : SecE3.E114ForE22R :=
  SecE3.e114ForE22R_of h.proved.e114LieCited hE114OneRes

theorem e22StatementCW (h : PartsW) (hE114ForE22R : SecE3.E114ForE22R) : E2.E22StatementC :=
  E2.E22N.e22StatementC_ofRL2 h.proved.e22StatementNoN E2.E22N.E111L.e111CoreMultiL2_holds
    hE114ForE22R

theorem tmpL4_4_2W (h : PartsW) : TmpL4_4_2 :=
  rem4_4_2_of h.inputs.in10.thm4_4_3

theorem stmt11_2_1W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3)
    (hE22StatementC : E2.E22StatementC) (hDerivedHallBorel : SecB.DerivedHallBorel)
    (hTmpL4_4_2 : TmpL4_4_2) : Stmt11_2_1 := by
  have hStmt4_4_13 := H13.stmt4_4_13_of hE22StatementC
  have hTmpL6_4_4_13 := Ch10.tmpL6_4_4_13_of hStmt4_4_13
  have hAS_E_3_38_perH := SecE3.as_e_3_38_perH_of_e22 hE22StatementC
  exact SecB.stmt11_2_1_of hDerivedHallBorel h.proved.asB51 h.proved.asB56 kindModuleFacts
      h.proved.tmpL6_3_2_2_two hTmpL6_4_4_13 hTmpL4_4_2 hAS_E_3_38_perH h.proved.theoremC58
      h.proved.as317Sylow h.proved.lem3_2_2_eight h.proved.factNotSmall443 SecB.factNPrimeNat_holds
      SecB.factNPrimeTwoNat_holds SecB.factCentralizerTwo_holds h.inputs.in10.thm3_3_1 h11_0_2
      h11_0_3

theorem stmt11_3_4W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (h11_2_2 : Stmt11_2_2) (h11_2_3 : Stmt11_2_3) (h11_3_3 : Stmt11_3_3) (h11_2_1 : Stmt11_2_1) :
    Stmt11_3_4 :=
  SecB.stmt11_3_4_of h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_1_0 h11_2_1 h11_2_2 h11_2_3 h11_3_3

end CFSG.Quasithin.Vol2.Ch11.Wire11
