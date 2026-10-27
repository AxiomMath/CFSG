module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def IsExtraGood {S : Type*} [Group S] (x : S) : Prop :=
  ∃ (H : Subgroup S) (N : ℕ), x ∈ H ∧ IsSpecialType 3 1 N ↥H ∧ 2 ≤ N

@[expose] def IsGenGood {S : Type*} [Group S] (σ : MulAut S) : Prop :=
  ∃ (k : ℕ) (g : Fin k → S) (y : S) (r : ℕ), r.Prime ∧ orderOf y = r ∧
    y ∈ closure (Set.range fun i => (g i)⁻¹ * σ (g i)) ∧ 3 * (k + 1) < dParam r

@[expose] def InvolGood (S : Type*) [Group S] : Prop :=
  ∀ σ : MulAut S, orderOf σ = 2 →
    (∃ x : S, orderOf x = 3 ∧ σ x = x⁻¹ ∧ IsExtraGood x) ∨ IsGenGood σ

@[expose] def InvolGen (S : Type*) [Group S] : Prop :=
  ∀ σ : MulAut S, orderOf σ = 2 → IsGenGood σ

@[expose] def InvolAt (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (n : ℕ), ¬ (t = .PSU ∧ n = 3) → ¬ (t = .PSp ∧ n = 2) →
    LieModel S t n 3 1 → InvolGood S

@[expose] def InvolGenG2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .G2 0 3 1 → InvolGen S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
