module

public import CFSG.Quasithin.Vol2.Ch11SecWire11J
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_0_2W (h : PartsW) (h3_2_5 : H13.Stmt3_2_5) : Stmt11_0_2 := by
  have hStmt3_2_8 := h.proved.lem3_2_8
  exact SecA.stmt11_0_2_of (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1) h3_2_5 hStmt3_2_8 h.proved.asB51
      h.proved.lem3_2_2_eight h.proved.facts02

theorem stmt11_0_3W (h : PartsW) (hTmpL6_3_2_2_six : TmpL6_3_2_2_six) (h3_2_5 : H13.Stmt3_2_5)
    (h11_0_2 : Stmt11_0_2) : Stmt11_0_3 :=
  SecA.stmt11_0_3_of h.proved.tmpL6_3_2_2_two h.proved.lem3_2_2_eight h.proved.tmpL6_3_2_2_four
    hTmpL6_3_2_2_six h3_2_5 h.proved.as_I_1_6 h.inputs.in10.thm3_3_1 h.proved.asB51 h.proved.asB56
    h.proved.theoremC58 h.proved.as317Sylow h.proved.factTwist kindModuleFacts
    SecB.factCentralizerTwo_holds h11_0_2

theorem tmpL6_4_2_13W (h : PartsW) : TmpL6_4_2_13 :=
  tmpL6_4_2_13_of h.inputs.in10.thm4_2_13

theorem stmt11_0_4W (h : PartsW) (h11_0_2 : Stmt11_0_2) : Stmt11_0_4 := by
  have hFacts04 : SecA.Facts04 := ⟨SecA.factTorusRank_holds, factA318Excl_holds⟩
  exact SecA.stmt11_0_4_of hFacts04 h.proved.a318Facts h.proved.a319Facts h.proved.a3_6
      h.proved.a3_8 h.inputs.in10.thm3_3_1 h.proved.as_I_1_6 h.proved.asB51 h.proved.asB56
      kindModuleFacts h.proved.tmpL6_3_2_2_two h11_0_2

theorem stmt11_1_1W (h : PartsW) (h11_0_2 : Stmt11_0_2) : Stmt11_1_1 :=
  SecA.stmt11_1_1_of h.proved.facts11 natFacts h11_0_2 h.proved.a3_6 h.proved.a3_7 h.proved.a3_8
    h.proved.a3_9 h.proved.a312ForSQTK

end CFSG.Quasithin.Vol2.Ch11.Wire11
