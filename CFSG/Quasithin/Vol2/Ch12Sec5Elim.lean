module

public import CFSG.Quasithin.Vol2.Ch12Sec5L4
public import CFSG.Quasithin.Vol2.Ch12Sec5L10
public import CFSG.Quasithin.Vol2.Ch12Sec5L11
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma4
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

theorem lemma12_5_4six_of_k1
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (hK₁ : K1Bad125) : Lemma12_5_4six :=
  fun _ _ _ _ _ _ F hH => S125L4.normalizer_V6_le h1222 h36 h37 h38 h39 h312 F hH
    (S125L4.centralizer_V6_le h1222 F hH (S125K1.l1_cComp_of h1222 h37 h38 h39 hK₁ F hH).2)

theorem lemma12_5_8_of_k1 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hK₁ : K1Bad125) (h7 : Lemma12_5_7) : Lemma12_5_8 :=
  fun G _ _ T L V F hH => S125L8.concl12_5_8_of h1222 F hH (h7 G T L V hH)
    (S125K1.l1_cComp_of h1222 h37 h38 h39 hK₁ F hH).2

theorem elim125_of_k1
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1228 : Stmt12_2_8) (h1229 : Stmt12_2_9) (h12210 : Stmt12_2_10)
    (h2211 : Stmt12_2_11') (h1241 : Lemma12_4_1) (h42 : AsB42) (hE63 : ASInputs.AS_E_6_3)
    (hE612 : ASInputs.AS_E_6_12) (hE22 : E2.E22StatementC) (hTor : E2.E22TorusCover)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (hK₁ : K1Bad125) : Elim125 := by
  have h4 := lemma12_5_4six_of_k1 h1222 h36 h37 h38 h39 h312 hK₁
  have h6 := lemma12_5_6_of h331 h1222 h323 h3228 h12210 hE63 hE612 h4
  have h7 := lemma12_5_7_of h331 h1222 h323 h3228 h4 h6
  have h8 := lemma12_5_8_of_k1 h1222 h37 h38 h39 hK₁ h7
  have h9 := lemma12_5_9_of h331 h1222 h323 h3228 h12210 h7 h8
  have h10 := lemma12_5_10_of h331 h1222 h323 h3228 h4 h6 h7 h9
  have h12 := lemma12_5_12_of h6 h7 h10 h2211
  have h1244 := lemma12_4_4_of h331 h1222 h323 hpre h3228 h1229 h12210 h1241 h42 hE63
  intro G _ _ T L V hH
  obtain ⟨F⟩ := frame125Exists_of h1222 G T L V hH
  have hL₁ := S125K1.l1_cComp_of h1222 h37 h38 h39 hK₁ F hH
  have hG₁ : ¬ Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro hle
    refine h1244 G T L V ⟨hH.hyp, Or.inr ⟨hH.quot, hH.card, ?_⟩⟩ hH.quot
    rw [frame125ZV_of h1222 G T L V F hH]
    exact (Subgroup.centralizer_le_normalizer _).trans hle
  exact final125_of' h331 h1222 h1228 hE22 hTor F hH hG₁ (lemma12_5_2_of h1222 G T L V F hH) hL₁
    (S125L4.centralizer_V3_le h1222 F hH hL₁.2) (h6 G T L V hH) (h7 G T L V hH)
    (h8 G T L V F hH) (h9 G T L V F hH) (h12 G T L V F hH)

end CFSG.Quasithin.H13
