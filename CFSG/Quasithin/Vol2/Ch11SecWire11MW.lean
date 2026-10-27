module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cGraphIso
public import CFSG.Quasithin.Vol2.Ch11L2Q5cRed
public import CFSG.Quasithin.Vol2.Ch11L2Q5cSchur
public import CFSG.Quasithin.Vol2.Ch11L2Q5cSzMoved
public import CFSG.Quasithin.Vol2.Ch11SecB35G2
public import CFSG.Quasithin.Vol2.Ch11SecBDerived35L2C
public import CFSG.Quasithin.Vol2.Ch11SecBK4Z
public import CFSG.Quasithin.Vol2.Ch11SecBK8D
public import CFSG.Quasithin.Vol2.Ch11SecBTCMain
public import CFSG.Quasithin.Vol2.Ch11SecBK2C
public import CFSG.Quasithin.Vol2.Ch11SecBK5A
public import CFSG.Quasithin.Vol2.Ch11SecBK5B
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW
public import CFSG.Quasithin.Vol2.Ch11SecWire11J

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_3_5W
    (h : PartsW) (h3_2_5 : H13.Stmt3_2_5) (h11_0_2 : Stmt11_0_2)
    (h11_0_3 : Stmt11_0_3) (h11_0_4 : Stmt11_0_4) (h11_2_2 : Stmt11_2_2) (h11_2_3 : Stmt11_2_3)
    (h11_3_3 : Stmt11_3_3) (hE22StatementC : E2.E22StatementC)
    (hDerivedHallBorel : SecB.DerivedHallBorel) (hTmpL4_4_2 : TmpL4_4_2) (h11_2_1 : Stmt11_2_1) :
    Stmt11_3_5 := by
  have hStmt3_2_8 := h.proved.lem3_2_8
  have hL2GraphIso := SecB.l2GraphIso_of h.proved.a312Facts h.proved.a3_6 h.proved.a3_7
      h.proved.a3_9 h.proved.stmt3_2_3 h3_2_5 hStmt3_2_8 h.proved.factG2Simple
  have hL2Graph := SecB.l2Graph_of_reduced h.proved.a312Facts h3_2_5 hStmt3_2_8
      h.proved.factG2Simple hL2GraphIso
  have hL2Suzuki := SecB.l2Suzuki_of_ten h.proved.a312Facts h.proved.a3_6 h.proved.a3_7
      h.proved.a3_9 h.proved.factMathieuOrders h3_2_5 hStmt3_2_8 h.proved.factG2Simple h.thm10_0_1
  have hL2Unitary := SecB.l2Unitary_of h.proved.a312Facts h.proved.a3_6 h.proved.a3_7 h.proved.a3_9
      h.proved.factMathieuOrders h3_2_5 hStmt3_2_8 h.proved.factG2Simple
  have hDerivedL2ListC := SecB.derivedL2ListC_of_parts (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1) SecB.l2Faithful_holds
      h.proved.l2Overgroup h.proved.l2NotJ4Orth hL2Graph hL2Suzuki hL2Unitary
  have hField11_3_5 := SecB.field11_3_5_of SecB.factNPrimeNat_holds SecB.factNPrimeTwoNat_holds
      natFacts hDerivedHallBorel h.proved.stmt4_4_13Lie hTmpL4_4_2 h.proved.factNotSmall443
      h.proved.lem3_2_2_eight h.proved.theoremC58 h.proved.as317Sylow SecB.factCentralizerTwo_holds
      h.proved.asB51 h.proved.asB56 kindModuleFacts h.proved.tmpL6_3_2_2_two SecB.factsVM_holds
      SecB.factPointTrans_holds KGNat.factG2DerivedOrder_holds h.inputs.in10.thmE6_3
      h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_0_4 h11_2_2 h11_2_3 h11_3_3
  exact SecB.stmt11_3_5_ofF natFacts hE22StatementC SecB.inputSchurSL2_holds hDerivedL2ListC
      hField11_3_5 (SecB.derivedTwoComponents_of
          CFSG.Quasithin.Vol2.KGNat.center_bot_and_dvd_card_normalizer_SL2) hDerivedHallBorel SecB.factCartanPower_holds
      SecB.factCentralizerTwo_holds h.proved.theoremC58 h.proved.as317Sylow h.proved.lem3_2_2_eight
      h.inputs.in10.thm3_3_1 h11_0_2 h11_0_4 h11_2_1 h11_2_2 h11_3_3

end CFSG.Quasithin.Vol2.Ch11.Wire11
