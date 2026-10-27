module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20z
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOne
import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

@[expose] def uc22pwCartanSU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, 2 < n → IsSU3 X n →
    ∀ (U : Sylow 2 X) (P : Type) [Group P], IsPGroup 2 P → ∀ ψ : P →* MulAut X,
      (∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) →
      ∀ e m' : ℕ, Odd m' → n = 2 ^ e * m' →
      ∃ E : Subgroup X, E ≤ normalizer ((U : Subgroup X) : Set X) ∧ IsCyclic E ∧
        Squarefree (Nat.card E) ∧ Odd (Nat.card E) ∧ piSet E = etaSet n ∧
        (∀ (g : P), ∀ x ∈ E, ψ g x ∈ E ⊔ (U : Subgroup X)) ∧
        (∀ (g : P), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ (U : Subgroup X)) ∧
        ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
          normalizer ((U : Subgroup X) : Set X) ⊔ Subgroup.zpowers w = ⊤

theorem uc22pwCartanRankOne_of_su3 (h : uc22pwCartanSU3) :
    uc22pwCartanRankOne := by
  intro X _ _ hq n hn hsh U P _ hP ψ hψ e m' hm' hnem
  rcases hsh with hsz | hl2 | hsu
  · exact uc22pwr1_literal_of_concl (uc22pwr1_concl_of_isSz hsz U hP ψ hψ hm' hnem)
  · exact uc22pwr1_literal_of_concl (uc22pwr1_concl_of_isL2 hl2 U hP ψ hψ hm' hnem)
  · exact h X hq n hn hsu U P hP ψ hψ e m' hm' hnem

end CFSG.LocalAnalysis.UniquenessCase.UC22
