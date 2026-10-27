module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.InvolutionTwoOrbitFourSet

open MulAction

theorem exists_set
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (a : G) (ha : a ^ 2 = 1)
    (hroom : (fixedBy X a).ncard + 4 ≤ Nat.card X) :
    ∃ T : Set X, T.ncard = 4 ∧ T ⊆ (fixedBy X a)ᶜ ∧
      ∀ y ∈ T, a • y ∈ T := by
  classical
  have hact (y : X) : a • (a • y) = y := by
    rw [← mul_smul, ← pow_two, ha, one_smul]
  have hsmall : (fixedBy X a).ncard < (Set.univ : Set X).ncard := by
    rw [Set.ncard_univ]
    omega
  obtain ⟨z, _, hz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hsmall
  have haz : a • z ≠ z := hz
  have hpairs : (fixedBy X a ∪ {z, a • z}).ncard < (Set.univ : Set X).ncard := by
    have hle := Set.ncard_union_le (fixedBy X a) {z, a • z}
    have hpair : ({z, a • z} : Set X).ncard = 2 := Set.ncard_pair haz.symm
    rw [Set.ncard_univ]
    omega
  obtain ⟨w, _, hw⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hpairs
  have hwfix : w ∉ fixedBy X a := fun h => hw (Or.inl h)
  have haw : a • w ≠ w := hwfix
  have hwz : w ≠ z := fun h => hw (Or.inr (Or.inl h))
  have hwaz : w ≠ a • z := fun h => hw (Or.inr (Or.inr h))
  have hawz : a • w ≠ z := by
    intro h
    have he := congrArg (fun y : X => a • y) h
    rw [hact] at he
    exact hwaz he
  have hawaz : a • w ≠ a • z := fun h => hwz (MulAction.injective a h)
  let T : Set X := {z, a • z, w, a • w}
  refine ⟨T, ?_, ?_, ?_⟩
  · have hnz : z ∉ ({a • z, w, a • w} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, haz.symm, hwz.symm, hawz.symm, false_or, not_false_eq_true]
    have hnaz : a • z ∉ ({w, a • w} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hwaz.symm, hawaz.symm, false_or, not_false_eq_true]
    change ({z, a • z, w, a • w} : Set X).ncard = 4
    rw [Set.ncard_insert_of_notMem hnz, Set.ncard_insert_of_notMem hnaz, Set.ncard_pair haw.symm]
  · intro y hy
    change y ∉ fixedBy X a
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy | hy
    · simpa only [hy] using hz
    · subst y
      intro h
      change a • (a • z) = a • z at h
      rw [hact] at h
      exact haz h.symm
    · simpa only [hy] using hwfix
    · subst y
      intro h
      change a • (a • w) = a • w at h
      rw [hact] at h
      exact haw h.symm
  · intro y hy
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl <;> simp only [hact, true_or, or_true, eq_self]

end FiveTransitive.InvolutionTwoOrbitFourSet

end CFSG
