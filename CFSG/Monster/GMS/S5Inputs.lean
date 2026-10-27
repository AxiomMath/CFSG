module

public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.GMS.Graph

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

variable {G : Type} [Group G] {d₀ : B}

section Helpers

private theorem eq_of_mem_zpowers_of_ne_one {z w : G} (hz : orderOf z = 2)
    (hw : w ∈ Subgroup.zpowers z) (hw1 : w ≠ 1) : w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← zpow_mod_orderOf, hz] at hw1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · simp [h] at hw1
  · simp [h]

end Helpers

end CFSG.Monster.GMS
