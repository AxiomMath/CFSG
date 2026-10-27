module

public import CFSG.Quasithin.Vol2.Ch11L2Q5cL2Orth
public import CFSG.Quasithin.Vol2.Ch11SecC37
public import CFSG.Quasithin.Vol2.Ch11SecH
public import CFSG.Quasithin.Vol2.Ch11SecO8G
public import CFSG.Quasithin.Vol2.Ch11SecBK8D
public import CFSG.Quasithin.Vol2.KGNatSL2NatBorel
public import CFSG.Quasithin.Vol2.KGNatSL3TransvIn
public import CFSG.Quasithin.Vol2.KGNatSp4BorelOdd
public import CFSG.Quasithin.Vol2.Ch11SecB36Main
public import CFSG.Quasithin.Vol2.Ch11SecBK2C
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW
public import CFSG.Quasithin.Vol2.Ch11SecWire11J
public import CFSG.Quasithin.Vol2.KGNatSL2Borel
public import CFSG.Quasithin.Vol2.KGNatSL2H
public import CFSG.Quasithin.Vol2.KGNatSL3Transv

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_3_6W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3) (h11_0_4 : Stmt11_0_4)
    (h11_2_2 : Stmt11_2_2) (h11_2_3 : Stmt11_2_3) (h11_3_3 : Stmt11_3_3) (h11_2_1 : Stmt11_2_1)
    (h11_3_5 : Stmt11_3_5) : Stmt11_3_6 :=
  SecB.stmt11_3_6_of SecB.factsVM_holds SecB.factsL2_holds SecB.factPointTrans_holds
    KGNat.factG2DerivedOrder_holds natFacts h.proved.as_G_1_6 h.inputs.in10.thmE6_3
    h.proved.as_E_6_12 h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_0_4 h11_2_1 h11_2_2 h11_2_3
    h11_3_3 h11_3_5

theorem stmt11_3_7W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_0_4 : Stmt11_0_4) (h11_2_2 : Stmt11_2_2)
    (h11_3_4 : Stmt11_3_4) (h11_3_5 : Stmt11_3_5) (h11_3_6 : Stmt11_3_6) : Stmt11_3_7 :=
  SecC.stmt11_3_7_of h11_0_2 h11_0_4 h11_2_2 h11_3_4 h11_3_5 h11_3_6 h.inputs.in10.thm3_3_1
    h.proved.theoremC58 h.proved.as317Sylow h.proved.lem3_2_2_eight h.proved.as_G_1_6 h.proved.asB51
    SecB.factCentralizerTwo_holds SecB.factFlagOneCentral_holds SecC.factAStarSylow_holds
    KGNat.factSL2NatFPF_holds natFacts KGNat.factSL2SylowNormalizer_holds KGNat.factSL2Borel_holds
    KGNat.factBorelOddSL3_holds KGNat.factBorelOddSp4_holds kindModuleFacts
    KGNat.factTorusLineSL3_holds KGNat.factTorusLineSp4_holds KGNat.factTransvPointSL3_holds
    KGNat.factTransvPointSp4_holds

theorem stmt11_3_2W (h : PartsW) (h11_0_2 : Stmt11_0_2) (h11_3_3 : Stmt11_3_3) (h11_3_4 : Stmt11_3_4)
    (h11_3_5 : Stmt11_3_5) (h11_3_6 : Stmt11_3_6) (h11_3_7 : Stmt11_3_7) : Stmt11_3_2 :=
  SecH.stmt11_3_2_of h11_0_2 h11_3_3 h11_3_4 h11_3_5 h11_3_6 h11_3_7 h.proved.as_G_1_6
    h.proved.lemI1_3_L2 KGNat.factG2DerivedOrder_holds KGNat.factTransvInSL3_holds
    KGNat.factAxisGroupSp4_holds KGNat.factSL2NatBorel_holds KGNat.factSL2TwoSylow_holds
    KGNat.factSL2BorelFPF_holds

theorem stmt11_4_1W (h : PartsW) (h11_0_0 : Stmt11_0_0) (h11_0_2 : Stmt11_0_2) (h11_0_3 : Stmt11_0_3)
    (h11_1_0 : Stmt11_1_0) (h11_1_1 : Stmt11_1_1) (h11_1_2 : Stmt11_1_2) (h11_2_2 : Stmt11_2_2)
    (h11_3_2 : Stmt11_3_2) : Stmt11_4_1 := by
  have hIn41 : SecE.In41 := ⟨h.inputs.in10.thm3_3_1, h.proved.lem3_2_2_eight, h11_0_0, h11_0_2,
      h11_0_3, h11_1_0, h11_1_1, h11_1_2, h11_2_2, h11_3_2⟩
  exact SecE.stmt11_4_1_of h.proved.facts41 hIn41

end CFSG.Quasithin.Vol2.Ch11.Wire11
