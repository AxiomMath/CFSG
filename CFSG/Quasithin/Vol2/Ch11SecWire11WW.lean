module

public import CFSG.Quasithin.Vol2.Ch11SecE42S1
public import CFSG.Quasithin.Vol2.Ch11SecE42S3Native
public import CFSG.Quasithin.Vol2.Ch11SecEK1B
public import CFSG.Quasithin.Vol2.Ch11SecO10N
public import CFSG.Quasithin.Vol2.Ch11SecO10ZJ
public import CFSG.Quasithin.Vol2.Ch11SecWire11L
public import CFSG.Quasithin.Vol2.Ch11SecE42
public import CFSG.Quasithin.Vol2.Ch11SecWire11FW
public import CFSG.Quasithin.Vol2.Ch11SecWire11G

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem stmt11_4_2W
    (h : PartsW) (h3_2_5 : H13.Stmt3_2_5) (h11_0_2 : Stmt11_0_2)
    (h11_0_3 : Stmt11_0_3) (h11_1_0 : Stmt11_1_0) (h11_0_4 : Stmt11_0_4) (h11_1_1 : Stmt11_1_1)
    (h11_1_5 : Stmt11_1_5) (h11_3_2 : Stmt11_3_2) (h11_4_1 : Stmt11_4_1) : Stmt11_4_2 := by
  have hParInFacts : SecE.ParInFacts := ⟨KGNat.factParInSL3_holds, SecE.factParInSp4_holds,
      SecE.factParInG2_holds⟩
  have hTmpL6_3_2_14 := h.proved.lem3_2_14 Ch10.a312ListFactsCat_holds h.proved.a3_7Cat
      h.proved.a3_8Cat
      h.proved.stmtFSUChoice (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1)
      Ch3T316W.theorem316Statement_holds
  have hStmt3_2_8 := h.proved.lem3_2_8
  have hObl11_4_2S1 := SecE.obl11_4_2S1_of h.proved.facts42 h.proved.facts42S1 h.proved.facts43
      pointFacts natFacts CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 h.proved.a3_7Cat
      h.proved.a3_9Cat h.proved.a312ForSQTKCat hTmpL6_3_2_14 h3_2_5 hStmt3_2_8
      (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1) h.proved.stmtFSUChoice h11_0_2
      h11_1_0 h11_1_1 h11_4_1
  have hObl11_4_2S3Lie := O10.obl11_4_2S3Lie_of h.proved.facts42 h.proved.facts42S3 h.proved.facts43
      h.proved.facts44 h.proved.facts15 pointFacts natFacts hParInFacts h.proved.a3_7Cat
      h.proved.a3_9Cat h.proved.stmtFSUChoice h.inputs.in10.thm3_3_1 h11_0_2 h11_0_3 h11_0_4 h11_1_0
      h11_1_1 h11_1_5 h11_3_2 h11_4_1
  have hObl11_4_2S3A7 := O10.obl11_4_2S3A7_of h.proved.facts42 h.proved.facts42S3 h.proved.facts43
      h.proved.facts15 pointFacts natFacts h.proved.a3_7Cat h.proved.a3_9Cat h.proved.stmtFSUChoice
      (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1) h3_2_5 hStmt3_2_8 h.proved.asB42 h.proved.asB51 h.proved.lem3_2_2_eight
      h11_0_2 h11_1_0 h11_1_1 h11_4_1
  have hObl11_4_2S3 := SecE.obl11_4_2S3_of_native h.proved.facts42 h.proved.facts42S3
      h.proved.facts43 pointFacts natFacts hParInFacts h.proved.a3_7Cat h.proved.a3_8Cat
      h.proved.a3_9Cat h3_2_5 hStmt3_2_8 (CFSG.Quasithin.H13.stmt7_0_1_of_A h.inputs.in10.thm7_0_1) h.proved.stmtFSUChoice h11_0_2
      h11_1_0 h11_1_1 h11_4_1 hObl11_4_2S3Lie hObl11_4_2S3A7
  exact SecE.stmt11_4_2_of h.proved.facts42 h.proved.facts43 pointFacts natFacts hParInFacts
      h.proved.sl2pSignalizerFact h.proved.a3_7Cat h.proved.a3_8Cat h.proved.a3_9Cat
      h.proved.a312ForSQTKCat hTmpL6_3_2_14 h11_0_2 h11_1_0 h11_1_1 h11_4_1 hObl11_4_2S1
      hObl11_4_2S3

end CFSG.Quasithin.Vol2.Ch11.Wire11
