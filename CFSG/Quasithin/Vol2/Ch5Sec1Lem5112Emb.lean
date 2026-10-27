module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Eq
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lt
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLie
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Vol2.Ch11.SecB (FactMathieuOrders)

theorem factMathieuOrders_holds :
    FactMathieuOrders :=
  ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2, CFSG.Sporadic.Mathieu.card_M22,
    CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2, CFSG.Sporadic.Mathieu.card_M24⟩

theorem stmt5_1_12_emb_of
    (hM : FactMathieuOrders) (hF : A314Facts) (hNL : A314NotLie2) (hM23 : FactM23L34)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h128 : Lemma128TwoAS) : Stmt5_1_12_emb := by
  intro G _ _ T M L H B D K₁ n k hyp hN hk hK₁ hKeq X Kh₁ hX hhat hlt
  have e : Emb512 G T M L H B D K₁ X Kh₁ n k := ⟨hyp, hN, hk, hK₁, hKeq, hX, hhat, hlt⟩
  rcases e.lt_or_eq with hlt₁ | heq
  · exact Or.inl (e.concl_of_lt h128 hlt₁)
  · exact Or.inr (e.concl_of_eq hM hF hNL hM23 hP h36 h312 heq)

theorem stmt5_1_12_of_inputs
    (h312 : Vol2Native.A312ForSQTKCat) (hF : A314Facts) (hM23 : FactM23L34)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h128 : Lemma128TwoAS) : Stmt5_1_12 :=
  stmt5_1_12_of Vol2Native.a39ForSQTKCat_proved
    (stmt5_1_12_emb_of factMathieuOrders_holds hF a314NotLie2_holds hM23 hP
      VolI.a36ForSQTK_holds (a312ForSQTK_of_cat h312) h128)

end CFSG.Quasithin.H13
