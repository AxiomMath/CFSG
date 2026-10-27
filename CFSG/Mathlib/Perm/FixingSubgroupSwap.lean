module

public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG.Perm

open Equiv MulAction

theorem fixingSubgroup_compl_le_of_swap_mem {α : Type*} [Finite α] [DecidableEq α]
    (s : Set α) (H : Subgroup (Perm α))
    (hswap : ∀ a ∈ s, ∀ b ∈ s, swap a b ∈ H) :
    fixingSubgroup (Perm α) sᶜ ≤ H := by
  let S : Set (Perm α) := {σ | ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ σ = swap a b}
  have hS : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  have hSH : Subgroup.closure S ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro σ ⟨a, ha, b, hb, hab, rfl⟩
    exact hswap a ha b hb
  intro σ hσ
  apply hSH
  refine (mem_closure_isSwap hS).mpr ⟨Set.toFinite _, ?_⟩
  intro x
  by_cases hx : σ x = x
  · rw [hx]
    exact mem_orbit_self x
  have hxs : x ∈ s := by
    by_contra h
    exact hx ((mem_fixingSubgroup_iff (Perm α)).mp hσ x h)
  have hσxs : σ x ∈ s := by
    by_contra h
    have hfix : σ (σ x) = σ x := (mem_fixingSubgroup_iff (Perm α)).mp hσ (σ x) h
    exact hx (σ.injective hfix)
  refine mem_orbit_iff.mpr ⟨⟨swap x (σ x), Subgroup.subset_closure ?_⟩, ?_⟩
  · exact ⟨x, hxs, σ x, hσxs, Ne.symm hx, rfl⟩
  · change swap x (σ x) x = σ x
    exact swap_apply_left x (σ x)

end CFSG.Perm

end
