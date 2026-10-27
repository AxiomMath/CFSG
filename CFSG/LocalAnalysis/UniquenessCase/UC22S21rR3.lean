module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rV
import CFSG.LocalAnalysis.UniquenessCase.UC22P22k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qx
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rS1Eq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_22R3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    D.sig = D.sig1 → CFSG.Open.evenRank G = 3 → False

theorem s22_8_of_standing22 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (hV : S22_V D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) : S22_8 D Ch := by
  have hid := uc22p22q_r613ident_of D st.sigma23 st.r6_1 st.sigma2
  have haut := uc22p22q_r613aut_of D st.sigma23 st.r6_1 st.sigma2 st.cent
  exact uc22p22k_s22_8_of D Ch (uc22p22q_r111_of D st.sigma23 st.r6_1 st.r6_11) hV
    (uc22p22q_r112_of D st.sigma23 st.r6_1 st.sigma2 hid st.cent haut) st.hyp612
    (uc22p22q_r6_13_of_print D st.sigma23 st.r6_1 st.sigma2 hid st.cent haut) hn3

theorem s21_22Use_of_s21_22R3 (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (hr77 : F07.R77Eq D) (he : CFSG.Open.evenRank G = 3) (hc : Nonempty (Ctx22b D Ch))
    (h8 : S22_8 D Ch) (h2118 : S21_18 D Ch) (h211 : S21_1 D Ch) (hR3 : S21_22R3 D Ch) :
    S21_22Use D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX
  obtain ⟨c'⟩ := hc
  have hS1 := uc22s21rs1_hinf_commutator_le_eq D st hr77 hH₁ hH₂
    (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF))
  have hU3 := s21_22U3_of_S22_8 D Ch st ⟨c'⟩ h8 h2118 h211 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1
  exact (hR3 h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 (h8 h1930 c') he).elim

theorem s22_9_of_s21_22R3
    (D : Data G) (Ch : Choice2011 G)
    (st : Standing22 D) (hr77 : F07.R77Eq D) (he : CFSG.Open.evenRank G = 3) (h204 : S20_4 D)
    (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hV : S22_V D Ch) (h2118 : S21_18 D Ch)
    (h211 : S21_1 D Ch) (hR3 : S21_22R3 D Ch) : S22_9 D Ch := fun h1930 c =>
  s22_9_of_S21_22Use D Ch
    (s21_22Use_of_s21_22R3 D Ch st hr77 he ⟨c⟩ (s22_8_of_standing22 D Ch st hV (hn3 h1930))
      h2118 h211 hR3) h204 hn3 hV h1930 c

end CFSG.LocalAnalysis.UniquenessCase.UC22
