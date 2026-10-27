module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Action.End

public section

namespace CFSG.Permutation.FixingGeneration

theorem fixingSubgroup_eq_sup_insert_zpowers_swap {I : Type*} [DecidableEq I]
    (S : Set I) {c d : I} (hc : c ∉ S) (hd : d ∉ S) (hcd : c ≠ d) :
    fixingSubgroup (Equiv.Perm I) S =
      fixingSubgroup (Equiv.Perm I) (insert d S) ⊔ Subgroup.zpowers (Equiv.swap c d) := by
  apply le_antisymm
  · intro σ hσ
    by_cases hσd : σ d = d
    · refine Subgroup.mem_sup_left ?_
      rw [mem_fixingSubgroup_iff]
      intro x hx
      rcases hx with rfl | hx
      · simpa using hσd
      · simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hσ x hx
    · let z : I := σ d
      have hzS : z ∉ S := by
        intro hz
        have hfix : σ z = z := by
          simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hσ z hz
        exact hσd (σ.injective (by simpa [z] using hfix))
      have hzd : z ≠ d := by
        intro h
        exact hσd (by simpa [z] using h)
      let e : Equiv.Perm I := Equiv.swap c z
      have he : e ∈ fixingSubgroup (Equiv.Perm I) (insert d S) := by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        rcases hx with rfl | hx
        · exact Equiv.swap_apply_of_ne_of_ne hcd.symm hzd.symm
        · exact Equiv.swap_apply_of_ne_of_ne
            (fun h => hc (h ▸ hx)) (fun h => hzS (h ▸ hx))
      have hconj : e * Equiv.swap c d * e⁻¹ = Equiv.swap z d := by
        rw [← Equiv.swap_apply_apply e c d]
        rw [show e c = z from Equiv.swap_apply_left c z,
          show e d = d from Equiv.swap_apply_of_ne_of_ne hcd.symm hzd.symm]
      have hzmem : Equiv.swap z d ∈
          fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
            Subgroup.zpowers (Equiv.swap c d) := by
        rw [← hconj]
        exact Subgroup.mul_mem
          (H := fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
            Subgroup.zpowers (Equiv.swap c d))
          (Subgroup.mul_mem
            (H := fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
              Subgroup.zpowers (Equiv.swap c d))
            (Subgroup.mem_sup_left he)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
          (Subgroup.inv_mem
            (H := fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
              Subgroup.zpowers (Equiv.swap c d))
            (Subgroup.mem_sup_left he))
      have hfixσ : Equiv.swap z d * σ ∈
          fixingSubgroup (Equiv.Perm I) (insert d S) := by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        rcases hx with rfl | hx
        · simp [z]
        · have hσx : σ x = x := by
            simpa using (mem_fixingSubgroup_iff (Equiv.Perm I)).mp hσ x hx
          have hxz : x ≠ z := fun h => hzS (h ▸ hx)
          have hxd : x ≠ d := fun h => hd (h ▸ hx)
          simp [hσx, Equiv.swap_apply_of_ne_of_ne hxz hxd]
      have hjoin : Equiv.swap z d * (Equiv.swap z d * σ) ∈
          fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
            Subgroup.zpowers (Equiv.swap c d) :=
        Subgroup.mul_mem
          (fixingSubgroup (Equiv.Perm I) (insert d S) ⊔
            Subgroup.zpowers (Equiv.swap c d)) hzmem (Subgroup.mem_sup_left hfixσ)
      simpa using hjoin
  · refine sup_le ?_ ?_
    · exact fixingSubgroup_antitone (Equiv.Perm I) I (Set.subset_insert d S)
    · rw [Subgroup.zpowers_le, mem_fixingSubgroup_iff]
      intro x hx
      exact Equiv.swap_apply_of_ne_of_ne
        (fun h => hc (h ▸ hx)) (fun h => hd (h ▸ hx))

end CFSG.Permutation.FixingGeneration

end
