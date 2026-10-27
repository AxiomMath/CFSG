module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_minimal_invariant {H V₀ R : Subgroup G} (hVR : V₀ < R)
    (hH : H ≤ normalizer (R : Set G)) :
    ∃ E₀ : Subgroup G, V₀ < E₀ ∧ E₀ ≤ R ∧ H ≤ normalizer (E₀ : Set G) ∧
      ∀ U : Subgroup G, V₀ ≤ U → U ≤ E₀ → H ≤ normalizer (U : Set G) → U = V₀ ∨ U = E₀ := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let S : Set (Subgroup G) := {U | V₀ < U ∧ U ≤ R ∧ H ≤ normalizer (U : Set G)}
  have hS : S.Nonempty := ⟨R, hVR, le_rfl, hH⟩
  obtain ⟨E₀, ⟨hVE, hER, hHE⟩, hmin⟩ :=
    Set.exists_min_image S (fun U : Subgroup G => Nat.card U) (Set.toFinite S) hS
  refine ⟨E₀, hVE, hER, hHE, fun U hVU hUE hHU => ?_⟩
  by_cases hU : U = V₀
  · exact Or.inl hU
  · right
    have hlt : V₀ < U := lt_of_le_of_ne hVU (Ne.symm hU)
    have hUS : U ∈ S := ⟨hlt, hUE.trans hER, hHU⟩
    exact Subgroup.eq_of_le_of_card_ge hUE (hmin U hUS)

end CFSG.LocalAnalysis.WeakClosure81

end
