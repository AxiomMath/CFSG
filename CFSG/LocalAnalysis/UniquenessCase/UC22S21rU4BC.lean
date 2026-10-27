module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4A
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_22U4BC (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    3 < CFSG.Open.evenRank G → ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 →
      (∃ n : ℕ, 2 < n ∧ (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n))) → False

theorem s21_22U4_of_U4BC (D : Data G) (Ch : Choice2011 G) (hc : Nonempty (Ctx22b D Ch))
    (h117 : R117W D) (h869P : F08.R869NPair D) (h8100E : R8100E D) (hV : S22_V D Ch)
    (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (hBC : S21_22U4BC D Ch) : S21_22U4 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2 hn
  obtain ⟨n, hn2, hLn⟩ := hn
  rcases hLn with hL2 | hSz
  · by_cases hpow : IsPowTwo n
    · exact s21_22U4A_of D Ch hc h117 h869P h8100E hV hn3 h1930 he hLC hc2 hn2 hL2 hpow
    · exact hBC h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2
        ⟨n, hn2, Or.inr ⟨hL2, hpow⟩⟩
  · exact hBC h1930 c H₁ hH₁ H₂ hH₂ hL hfX hS1 hU3 he L hLC hc2 ⟨n, hn2, Or.inl hSz⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
