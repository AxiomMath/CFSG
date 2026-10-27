module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem false_of_inf_centralizer_eq (h : Counterexample p A θ) {W : Subgroup G}
    (hAW : A ≤ Subgroup.normalizer (W : Set G)) (hcop : Nat.Coprime p (Nat.card W))
    (hB : signalizerMcBrideHypothesisB p W)
    (hC : ∀ a ∈ A, a ≠ 1 → W ⊓ Subgroup.centralizer {a} = θ a) : False := by
  have hmem : W ∈ Msig p A θ := ⟨hAW, hcop, fun a ha ha1 => (hC a ha ha1).le, hB⟩
  apply h.notComplete
  refine (isCompleteIn_iff_exists_apply_le h.prime h.elemAbelian h.rank_two_le h.isFunctor
    h.hypC).mpr ⟨W, hmem, fun a ha ha1 => ?_⟩
  rw [← hC a ha ha1]
  exact inf_le_left

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
