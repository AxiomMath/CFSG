module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def K_19_21_opp (S : Type) [Group S] : Prop :=
  ∀ U : Sylow 2 S, (U : Subgroup S) ≠ ⊥ → ∀ r : ℕ, r.Prime → r ≠ 2 →
    ∀ Ehat : Subgroup (MulAut S), IsPGroup r Ehat →
    (∀ α ∈ Ehat, (U : Subgroup S).map (MulEquiv.toMonoidHom α) = U) →
    ∃ (H : Subgroup S) (n : S), H ≤ normalizer ((U : Subgroup S) : Set S) ∧
      n ∈ normalizer (H : Set S) ∧ (∀ α ∈ Ehat, H.map (MulEquiv.toMonoidHom α) = H) ∧
      (∀ α ∈ Ehat, n⁻¹ * α n ∈ H) ∧ ∀ h ∈ H, (U : Subgroup S) ⊔ zpowers (h * n) = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
