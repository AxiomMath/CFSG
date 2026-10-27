module

public import CFSG.Quasithin.Vol2.Ch11SecD551S
public import CFSG.Quasithin.Vol2.Ch11SecD557
public import CFSG.Quasithin.Vol2.Ch11SecD557R
public import CFSG.Quasithin.Vol2.Ch11SecD557U
public import CFSG.Quasithin.Vol2.Ch11SecE43
public import CFSG.Quasithin.Vol2.Ch11SecE44C
public import CFSG.Quasithin.Vol2.Ch11SecEK2C
public import CFSG.Quasithin.Vol2.Ch11SecFMain
public import CFSG.Quasithin.Vol2.Ch11SecGMain
public import CFSG.Quasithin.Vol2.Ch11SecJDick4
public import CFSG.Quasithin.Vol2.Ch11SecJEnd3
public import CFSG.Quasithin.Vol2.Ch11SecJMain
public import CFSG.Quasithin.Vol2.Ch11SecO1E
public import CFSG.Quasithin.Vol2.Ch11SecO1bF
public import CFSG.Quasithin.Vol2.Ch11SecO1bN
public import CFSG.Quasithin.Vol2.Ch11SecO1bR
public import CFSG.Quasithin.Vol2.Ch11SecO2E
public import CFSG.Quasithin.Vol2.Ch11SecO2H
public import CFSG.Quasithin.Vol2.Ch11SecO2I
public import CFSG.Quasithin.Vol2.Ch11SecO3Alpha
public import CFSG.Quasithin.Vol2.Ch11SecO3CXi
public import CFSG.Quasithin.Vol2.Ch11SecO3Y
public import CFSG.Quasithin.Vol2.Ch11SecO6E
public import CFSG.Quasithin.Vol2.Ch11SecO8HG
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW
public import CFSG.Quasithin.Vol2.Ch11SecWire11J
public import CFSG.Quasithin.Vol2.Ch11SecWire11L

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_4_3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0) (h11_1_1 : Stmt11_1_1)
    (h11_1_2 : Stmt11_1_2) (h11_2_3 : Stmt11_2_3) (h11_3_2 : Stmt11_3_2) (h11_4_1 : Stmt11_4_1)
    (h11_4_2 : Stmt11_4_2) : Stmt11_4_3 :=
  SecE.stmt11_4_3_of pointFacts h.proved.facts43 h.inputs.in10.thm3_3_1 h11_0_2 h11_1_0 h11_1_1
    h11_1_2 h11_2_3 h11_3_2 h11_4_1 h11_4_2

theorem as_p778_nParamSW (h : PartsW) (hE114OneResRest : E2.E22N.E114OneResRest) :
    SecB.AS_p778_nParamS :=
  E2.E22N.asP778NParamS_ofRestL2 E2.E22N.E111L.e111CoreMultiL2_holds hE114OneResRest
    h.proved.e22StatementNoN

theorem stmt11_4_4SW (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (h11_0_4 : Stmt11_0_4) (h11_1_1 : Stmt11_1_1) (hTmpL4_4_2 : TmpL4_4_2) (h11_4_1 : Stmt11_4_1)
    (h11_4_2 : Stmt11_4_2) : SecE.Stmt11_4_4S :=
  SecE.stmt11_4_4S_of h.proved.facts44 h.proved.facts43 pointFacts h.proved.factNotSmall443
    SecB.factBorelComm_holds h.proved.stmt4_4_13Lie hTmpL4_4_2 h.proved.a3_7Cat h.proved.a3_9Cat
    h.inputs.in10.thm3_3_1 h.proved.lem3_2_2_eight h11_0_2 h11_0_3 h11_0_4 h11_1_0 h11_1_1 h11_4_1
    h11_4_2

theorem stmt11_5_1W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0) (h11_1_2 : Stmt11_1_2)
    (h11_2_2 : Stmt11_2_2) (h11_4_1 : Stmt11_4_1) (h11_4_3 : Stmt11_4_3)
    (hAs_p778_nParamS : SecB.AS_p778_nParamS) (h11_4_4S : SecE.Stmt11_4_4S) : Stmt11_5_1 :=
  SecD.stmt11_5_1_ofS hAs_p778_nParamS SecD.factSolvPointG2_holds SecD.sl2pMultFact_holds
    h.proved.l2pSignalizerFact KGNat.pointsTIFact_holds h.inputs.in10.thm3_3_1 h11_0_2 h11_1_0
    h11_1_2 h11_2_2 h11_4_1 h11_4_3 h11_4_4S

theorem stmt11_5_3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (h11_2_2 : Stmt11_2_2) (h11_2_5 : Stmt11_2_5) (h11_4_1 : Stmt11_4_1) (h11_4_2 : Stmt11_4_2)
    (h11_4_3 : Stmt11_4_3) (hAs_p778_nParamS : SecB.AS_p778_nParamS) (h11_4_4S : SecE.Stmt11_4_4S)
    (h11_5_1 : Stmt11_5_1) : Stmt11_5_3 :=
  SecE.stmt11_5_3_ofS SecD.twoPointsFact_holds SecD.cardVFact_holds SecD.rankV2Fact_holds
    SecD.pointCommFact_holds h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_1_0 h11_2_2 h11_2_5 h11_4_1
    h11_4_2 h11_4_3 hAs_p778_nParamS h11_4_4S h11_5_1

theorem stmt11_5_6W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0)
    (h11_1_1 : Stmt11_1_1) (h11_1_2 : Stmt11_1_2) (h11_4_1 : Stmt11_4_1) (h11_4_3 : Stmt11_4_3)
    (h11_5_1 : Stmt11_5_1) : Stmt11_5_6 := by
  have hGap11_5_6Three := SecD.gap11_5_6Three_of h.proved.factCCompTorus h.proved.prop121Three
      h.proved.facts44 SecD.cartanFact_holds cartanFacts natFacts KGNat.pointsTIFact_holds
      h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_1_0 h11_4_1 h11_4_3 h11_5_1
  exact SecD.stmt11_5_6_of hGap11_5_6Three SecD.cartanFact_holds h.proved.factM2Case1
      h.proved.factM2Case1Prime h.proved.l2pSignalizerFact KGNat.pointsTIFact_holds natFacts h11_0_2
      h11_1_0 h11_1_1 h11_1_2 h11_4_1 h11_4_3 h11_5_1

theorem stmt11_5_7SL3W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0)
    (h11_1_1 : Stmt11_1_1) (h11_1_2 : Stmt11_1_2) (h11_4_1 : Stmt11_4_1) (h11_4_3 : Stmt11_4_3)
    (h11_5_4 : Stmt11_5_4) (h11_5_5 : Stmt11_5_5) (h11_5_6 : Stmt11_5_6) : SecD.Stmt11_5_7SL3 := by
  have hObl11_5_7SL3Small := SecD.obl11_5_7SL3Small_of h.proved.factCase1NormL1
      h.proved.factCase1GL8 KGNat.pointsTIFact_holds KGNat.factG2DerivedOrder_holds
      SecD.natV3Fact_holds h.inputs.in10.thm3_3_1 h11_0_2 h11_1_0 h11_1_1 h11_1_2 h11_4_1 h11_4_3
      h11_5_4 h11_5_5
  have hObl11_5_7SL3BigCore := SecJ.obl11_5_7SL3BigCore_of SecJ.factNatPairEnd_holds
      SecJ.factDicksonGL2_holds KGNat.factG2DerivedOrder_holds SecD.natV3Fact_holds
      h.inputs.in10.thm3_3_1 h11_0_2 h11_1_0 h11_4_1 h11_4_3 h11_5_4 h11_5_5 h11_5_6
  have hObl11_5_7SL3Big := SecD.obl11_5_7SL3Big_of hObl11_5_7SL3BigCore
      KGNat.factG2DerivedOrder_holds SecD.natV3Fact_holds h11_0_2 h11_1_0 h11_4_1 h11_5_4 h11_5_5
  have hObl11_5_7SL3End := SecD.obl11_5_7SL3End_of hObl11_5_7SL3Small hObl11_5_7SL3Big
      h.proved.as_I_1_6 KGNat.factG2DerivedOrder_holds SecD.commLOneSL3Fact_holds
      SecD.natV3Fact_holds h11_0_2 h11_1_0 h11_4_1 h11_5_4 h11_5_5
  exact SecD.stmt11_5_7SL3_of hObl11_5_7SL3End KGNat.factG2DerivedOrder_holds
      SecD.torusFixSL3Fact_holds SecD.commLOneSL3Fact_holds SecD.natV3Fact_holds h11_0_2 h11_1_0
      h11_4_1 h11_4_3 h11_5_4 h11_5_5 h11_5_6

theorem stmt11_5_7Sp4W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3)
    (h11_1_0 : Stmt11_1_0) (h11_1_2 : Stmt11_1_2) (h11_1_3 : Stmt11_1_3) (h11_1_4 : Stmt11_1_4)
    (h11_1_5 : Stmt11_1_5) (h11_4_1 : Stmt11_4_1) (h11_4_3 : Stmt11_4_3) (h11_5_4 : Stmt11_5_4)
    (h11_5_5 : Stmt11_5_5) (h11_5_6 : Stmt11_5_6) : SecD.Stmt11_5_7Sp4 := by
  have hSp4Facts : SecF.Sp4Facts := ⟨SecF.factSp4CartanFree_holds, SecF.factSp4Z_holds,
      SecF.factSp4RadLine_holds, SecF.factSp4VL2_holds, SecF.factSp4L2Rad_holds⟩
  have hObl11_5_7Sp4CX := SecF.obl11_5_7Sp4CX_of hSp4Facts natFacts h11_0_2 h11_0_3 h11_1_0 h11_1_3
      h11_4_1 h11_4_3 h11_5_4 h11_5_6
  have hObl11_5_7Sp4Alpha := SecF.obl11_5_7Sp4Alpha_of h11_0_2 h11_1_0 h11_1_2 h11_4_1 h11_4_3
  have hObl11_5_7Sp4Y := SecF.obl11_5_7Sp4Y_of hSp4Facts h11_0_2 h11_0_3 h11_1_0 h11_1_3 h11_1_4
      h11_4_1 h11_4_3 h11_5_4 h11_5_5 h11_5_6
  exact SecF.stmt11_5_7Sp4_of hSp4Facts SecF.factSp4VL1_holds SecF.factSp4V3R1_holds
      SecF.factSp4ZCent_holds SecF.factSp4Opp_holds SecF.factSp4Trans_holds SecF.factSp4Gen_holds
      SecF.factSp4RL_holds h.proved.facts15 natFacts h.proved.as_I_1_3_Sp4 h.inputs.thmC1_32
      hObl11_5_7Sp4CX hObl11_5_7Sp4Alpha hObl11_5_7Sp4Y h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3
      h11_1_0 h11_1_3 h11_1_4 h11_1_5 h11_4_1 h11_4_3 h11_5_4 h11_5_5 h11_5_6

theorem stmt11_5_8W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_1_0 : Stmt11_1_0) (h11_1_1 : Stmt11_1_1)
    (h11_1_2 : Stmt11_1_2) (h11_2_2 : Stmt11_2_2) (h11_4_1 : Stmt11_4_1) (h11_4_2 : Stmt11_4_2)
    (h11_4_3 : Stmt11_4_3) (h11_5_1 : Stmt11_5_1) (h11_5_5 : Stmt11_5_5) (h11_5_6 : Stmt11_5_6)
    (h11_5_7 : Stmt11_5_7) : Stmt11_5_8 :=
  SecG.stmt11_5_8_of h.proved.factTransv11_5_8 h.proved.factCase1Shape h.proved.factCase1PrimeAct
    SecG.commEndStableFact_holds SecG.r1CommFact_holds SecG.pointConjFact_holds
    SecG.r1CorankFact_holds KGNat.pointsTIFact_holds SecD.cardVFact_holds h.inputs.in10.thm3_3_1
    h.proved.lem3_2_2_eight h11_0_2 h11_1_0 h11_1_1 h11_1_2 h11_2_2 h11_4_1 h11_4_2 h11_4_3 h11_5_1
    h11_5_5 h11_5_6 h11_5_7

theorem stmt11_0_1W (h : PartsW) (h11_0_0 : Stmt11_0_0) (h11_1_0 : Stmt11_1_0) (h11_5_3 : Stmt11_5_3)
    (h11_5_7 : Stmt11_5_7) (h11_5_8 : Stmt11_5_8) : H13.Stmt11_0_1 :=
  stmt11_0_1_of_steps h.proved.rankTwoQuasisimple h11_0_0 h.proved.stmtFSUChoice h11_1_0 h11_5_3
    h11_5_7 h11_5_8

end CFSG.Quasithin.Vol2.Ch11.Wire11
