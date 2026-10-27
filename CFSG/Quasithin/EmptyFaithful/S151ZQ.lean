module

public import CFSG.Quasithin.EmptyFaithful.S151ZP

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ}

@[expose] def nodeSet (n : ℕ) : Set ℕ := {x | IsNode n x}

theorem mem_nodeSet {x : ℕ} : x ∈ nodeSet n ↔ 1 ≤ x ∧ x < n := Iff.rfl

theorem Ut_eq_QI_nodeSet : Ut n = QI n (nodeSet n) := Ut_eq_QI

theorem index_single {i : ℕ} (hi : IsNode n i) :
    (Ut n).relIndex (QI n (nodeSet n \ {i})) = 3 := by
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by have := hi.1; omega⟩
  obtain ⟨hi1, hi2⟩ := hi
  have hC : ∀ x ∈ nodeSet n \ {p + 1}, IsNode n x := fun x hx => hx.1
  have hset : insert (p + 1) (nodeSet n \ {p + 1}) = nodeSet n := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff, mem_nodeSet]
    constructor
    · rintro (rfl | h)
      · exact ⟨hi1, hi2⟩
      · exact h.1
    · intro h
      by_cases hx : x = p + 1
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩
  have hstep := qi_step (n := n) (p := p) (k := 2) hC (le_refl 2) (by omega)
    (by
      by_cases hp : p = 0
      · exact Or.inl hp
      · right
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        omega)
    (by
      by_cases hp : p + 2 = n
      · exact Or.inl hp
      · right
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        omega)
    (by simp)
  rw [hset, ← Ut_eq_QI_nodeSet] at hstep
  exact step_two_val hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2

theorem index_double {i j : ℕ} (hi : IsNode n i) (hj : IsNode n j) (hij : i < j) :
    (Ut n).relIndex (QI n (nodeSet n \ {i, j})) = 9 ∨
      (Ut n).relIndex (QI n (nodeSet n \ {i, j})) = 21 := by
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  set C : Set ℕ := nodeSet n \ {i, j} with hCdef
  have hC : ∀ x ∈ C, IsNode n x := fun x hx => hx.1
  have hmemC : ∀ x, x ∈ C ↔ (1 ≤ x ∧ x < n) ∧ x ≠ i ∧ x ≠ j := by
    intro x
    simp only [hCdef, Set.mem_sdiff, mem_nodeSet, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  have hC' : ∀ x ∈ insert i C, IsNode n x := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨hi1, hi2⟩
    · exact hC x hx
  have hset : insert j (insert i C) = nodeSet n := by
    ext x
    simp only [Set.mem_insert_iff, hmemC, mem_nodeSet]
    constructor
    · rintro (rfl | rfl | h)
      · exact ⟨hj1, hj2⟩
      · exact ⟨hi1, hi2⟩
      · exact h.1
    · intro h
      by_cases hxj : x = j
      · exact Or.inl hxj
      · by_cases hxi : x = i
        · exact Or.inr (Or.inl hxi)
        · exact Or.inr (Or.inr ⟨h, hxi, hxj⟩)
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
  have hs1 : (QI n (insert (p + 1) C)).relIndex (QI n C) = 3 ∨
      (QI n (insert (p + 1) C)).relIndex (QI n C) = 7 := by
    have hpC : p = 0 ∨ p ∈ C := by
      by_cases hp : p = 0
      · exact Or.inl hp
      · right
        rw [hmemC]
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    have hnot : p + 1 ∉ C := by
      rw [hmemC]
      tauto
    by_cases hadj : p + 1 + 1 = j
    · have h := qi_step (n := n) (p := p) (k := 3) hC (by omega) (by omega) hpC
        (by
          by_cases hq : p + 3 = n
          · exact Or.inl hq
          · right
            rw [hmemC]
            exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩) hnot
      exact step_three_val h.1 h.2.1 h.2.2.1 h.2.2.2
    · have h := qi_step (n := n) (p := p) (k := 2) hC (le_refl 2) (by omega) hpC
        (Or.inr (by
          rw [hmemC]
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩)) hnot
      exact Or.inl (step_two_val h.1 h.2.1 h.2.2.1 h.2.2.2)
  obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
  have hs2 : (Ut n).relIndex (QI n (insert (p + 1) C)) = 3 := by
    have hqC : q = 0 ∨ q ∈ insert (p + 1) C := by
      right
      by_cases hqi : q = p + 1
      · exact Or.inl hqi
      · right
        rw [hmemC]
        exact ⟨⟨by omega, by omega⟩, hqi, by omega⟩
    have hnot : q + 1 ∉ insert (p + 1) C := by
      simp only [Set.mem_insert_iff, hmemC]
      omega
    have h := qi_step (n := n) (p := q) (k := 2) hC' (le_refl 2) (by omega) hqC
      (by
        by_cases hq : q + 2 = n
        · exact Or.inl hq
        · right
          simp only [Set.mem_insert_iff, hmemC]
          right
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩) hnot
    rw [hset, ← Ut_eq_QI_nodeSet] at h
    exact step_two_val h.1 h.2.1 h.2.2.1 h.2.2.2
  have hUQ : Ut n ≤ QI n (insert (p + 1) C) := Ut_le_QI n _
  have hQC : QI n (insert (p + 1) C) ≤ QI n C :=
    (QI_le_QI_iff hC).mpr (Set.subset_insert _ _)
  have hmul := Subgroup.relIndex_mul_relIndex (Ut n) (QI n (insert (p + 1) C)) (QI n C) hUQ hQC
  rw [← hmul, hs2]
  rcases hs1 with h | h
  · rw [h]
    left
    rfl
  · rw [h]
    right
    rfl

end CFSG.Quasithin.FLc
