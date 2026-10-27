module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

private theorem alternatingGroup_le_of_forall_mem {K : Subgroup (Perm (Fin 7))}
    (h : ∀ i : Fin 5, altThreeCyclePerm i ∈ K) : alternatingGroup (Fin 7) ≤ K := by
  have h' := (Subgroup.closure_le K).2 (Set.range_subset_iff.2 h)
  rw [closure_altThreeCyclePerm] at h'
  exact h'

private theorem alternatingGroup_le_closure_of_words_two {x1 x2 x3 : Perm (Fin 7)}
    (h3 : x1 * x3 * x2 * x1 * (x3 * x1 * x2) ^ 2 = (altThreeCyclePerm (0 : Fin 5))⁻¹)
    (h4 : x1 * (x2 * x1 * x3) ^ 2 * x1 * x2 * x3 = (altThreeCyclePerm (1 : Fin 5))⁻¹)
    (h5 : x3 * x2 * x3 * x1 * x2 * x1 * x3 * x2 * x3 * x1 = (altThreeCyclePerm (2 : Fin 5))⁻¹)
    (h6 : (x1 * x2 * x1 * x3 * x1 * x2) ^ 2 = (altThreeCyclePerm (3 : Fin 5))⁻¹)
    (h7 : (x1 * x2) ^ 2 * x3 * x1 * x2 * x1 * x3 * x2 * x1 * x2 =
      (altThreeCyclePerm (4 : Fin 5))⁻¹) :
    alternatingGroup (Fin 7) ≤ Subgroup.closure {x1, x2, x3} := by
  have hx1 : x1 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have hx2 : x2 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have hx3 : x3 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have m3 : altThreeCyclePerm (0 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h3]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m4 : altThreeCyclePerm (1 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h4]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m5 : altThreeCyclePerm (2 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h5]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m6 : altThreeCyclePerm (3 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h6]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m7 : altThreeCyclePerm (4 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h7]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  refine alternatingGroup_le_of_forall_mem fun i => ?_
  fin_cases i
  exacts [m3, m4, m5, m6, m7]

private theorem alternatingGroup_le_closure_of_words_three {x1 x2 x3 : Perm (Fin 7)}
    (h3 : x1 * x2 * x3 * (x1 * x2) ^ 2 * x1 * x3 * x2 * x1 * x2 =
      (altThreeCyclePerm (0 : Fin 5))⁻¹)
    (h4 : (x1 * x2) ^ 2 * x3 * (x1 * x2) ^ 2 * x1 * x3 * x2 = (altThreeCyclePerm (1 : Fin 5))⁻¹)
    (h5 : (x3 * (x1 * x2) ^ 2 * x1) ^ 2 = (altThreeCyclePerm (2 : Fin 5))⁻¹)
    (h6 : ((x2 * x1) ^ 2 * x3 * x1) ^ 2 = (altThreeCyclePerm (3 : Fin 5))⁻¹)
    (h7 : (x2 * x1 * x3 * x1 * x2 * x1) ^ 2 = (altThreeCyclePerm (4 : Fin 5))⁻¹) :
    alternatingGroup (Fin 7) ≤ Subgroup.closure {x1, x2, x3} := by
  have hx1 : x1 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have hx2 : x2 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have hx3 : x3 ∈ Subgroup.closure {x1, x2, x3} := Subgroup.subset_closure (by simp)
  have m3 : altThreeCyclePerm (0 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h3]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m4 : altThreeCyclePerm (1 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h4]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m5 : altThreeCyclePerm (2 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h5]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m6 : altThreeCyclePerm (3 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h6]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  have m7 : altThreeCyclePerm (4 : Fin 5) ∈ Subgroup.closure {x1, x2, x3} := by
    rw [← Subgroup.inv_mem_iff, ← h7]
    repeat' first | assumption | apply Subgroup.pow_mem | apply Subgroup.mul_mem
  refine alternatingGroup_le_of_forall_mem fun i => ?_
  fin_cases i
  exacts [m3, m4, m5, m6, m7]

private theorem exists_alternatingGroup_le_closure_two : ∃ g₁ g₂ : Perm (Fin 7),
    alternatingGroup (Fin 7) ≤ Subgroup.closure {swap 0 1 * swap 2 3,
      g₁ * (swap 0 1 * swap 2 3) * g₁⁻¹, g₂ * (swap 0 1 * swap 2 3) * g₂⁻¹} :=
  ⟨swap 1 4 * swap 1 2, swap 1 5 * swap 3 6,
    alternatingGroup_le_closure_of_words_two (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

private theorem exists_alternatingGroup_le_closure_three : ∃ g₁ g₂ : Perm (Fin 7),
    alternatingGroup (Fin 7) ≤ Subgroup.closure {swap 0 1 * swap 2 3 * swap 4 5,
      g₁ * (swap 0 1 * swap 2 3 * swap 4 5) * g₁⁻¹,
      g₂ * (swap 0 1 * swap 2 3 * swap 4 5) * g₂⁻¹} :=
  ⟨swap 2 6 * swap 2 4, swap 1 6 * swap 1 4,
    alternatingGroup_le_closure_of_words_three (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

private theorem alternatingGroup_le_closure_image_conj {S : Set (Perm (Fin 7))}
    (k : Perm (Fin 7)) (h : alternatingGroup (Fin 7) ≤ Subgroup.closure S) :
    alternatingGroup (Fin 7) ≤ Subgroup.closure ((fun x => k * x * k⁻¹) '' S) := by
  intro a ha
  have h1 : k⁻¹ * a * k ∈ Subgroup.closure S := h (Subgroup.Normal.conj_mem inferInstance a ha _)
  have h2 : k * (k⁻¹ * a * k) * k⁻¹ ∈ (Subgroup.closure S).map (MulAut.conj k).toMonoidHom :=
    ⟨_, h1, rfl⟩
  rw [MonoidHom.map_closure] at h2
  have e : k * (k⁻¹ * a * k) * k⁻¹ = a := by group
  rw [e] at h2
  exact h2

private theorem exists_alternatingGroup_le_closure_of_isConj {s s' : Perm (Fin 7)}
    (hc : IsConj s s') (h : ∃ g₁ g₂ : Perm (Fin 7),
      alternatingGroup (Fin 7) ≤ Subgroup.closure {s, g₁ * s * g₁⁻¹, g₂ * s * g₂⁻¹}) :
    ∃ g₁ g₂ : Perm (Fin 7),
      alternatingGroup (Fin 7) ≤ Subgroup.closure {s', g₁ * s' * g₁⁻¹, g₂ * s' * g₂⁻¹} := by
  obtain ⟨k, rfl⟩ := isConj_iff.1 hc
  obtain ⟨g₁, g₂, h⟩ := h
  refine ⟨k * g₁ * k⁻¹, k * g₂ * k⁻¹, ?_⟩
  have e1 : k * g₁ * k⁻¹ * (k * s * k⁻¹) * (k * g₁ * k⁻¹)⁻¹ = k * (g₁ * s * g₁⁻¹) * k⁻¹ := by
    group
  have e2 : k * g₂ * k⁻¹ * (k * s * k⁻¹) * (k * g₂ * k⁻¹)⁻¹ = k * (g₂ * s * g₂⁻¹) * k⁻¹ := by
    group
  rw [e1, e2]
  have himg : (fun x => k * x * k⁻¹) '' {s, g₁ * s * g₁⁻¹, g₂ * s * g₂⁻¹} =
      {k * s * k⁻¹, k * (g₁ * s * g₁⁻¹) * k⁻¹, k * (g₂ * s * g₂⁻¹) * k⁻¹} := by
    simp only [Set.image_insert_eq, Set.image_singleton]
  rw [← himg]
  exact alternatingGroup_le_closure_image_conj k h

private theorem cycleType_two :
    (swap (0 : Fin 7) 1 * swap 2 3).cycleType = Multiset.replicate 2 2 := by
  have h := cycleType_swap_mul_swap_of_nodup (α := Fin 7) (x := 0) (y := 1) (z := 2) (t := 3)
    (by decide)
  simpa using h

private theorem cycleType_three :
    (swap (0 : Fin 7) 1 * swap 2 3 * swap 4 5).cycleType = Multiset.replicate 3 2 := by
  have hd : Disjoint (swap (0 : Fin 7) 1 * swap 2 3) (swap 4 5) :=
    Disjoint.mul_left
      (disjoint_swap_swap (α := Fin 7) (x := 0) (y := 1) (z := 4) (t := 5) (by decide))
      (disjoint_swap_swap (α := Fin 7) (x := 2) (y := 3) (z := 4) (t := 5) (by decide))
  rw [Disjoint.cycleType_mul hd, cycleType_two,
    isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (4 : Fin 7) ≠ 5))]
  rw [← Multiset.replicate_one, ← Multiset.replicate_add]

private theorem cycleType_eq_replicate {s : Perm (Fin 7)} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hsw : ¬ s.IsSwap) :
    s.cycleType = Multiset.replicate 2 2 ∨ s.cycleType = Multiset.replicate 3 2 := by
  obtain ⟨k, hk⟩ : ∃ k, s.cycleType = Multiset.replicate k 2 :=
    ⟨_, cycleType_of_pow_prime_eq_one (by rwa [pow_two])⟩
  have hpos : 0 < Multiset.card s.cycleType := card_cycleType_pos.2 hs1
  rw [hk, Multiset.card_replicate] at hpos
  have hle := sum_cycleType_le s
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hle
  have hne : k ≠ 1 := fun h => hsw (isSwap_iff_cycleType.2 (by rw [hk, h, Multiset.replicate_one]))
  rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
  · exact Or.inl hk
  · exact Or.inr hk

theorem exists_conj_alternatingGroup_le_closure {s : Perm (Fin 7)} (hs : s * s = 1) (hs1 : s ≠ 1)
    (hsw : ¬ s.IsSwap) : ∃ g₁ g₂ : Perm (Fin 7),
      alternatingGroup (Fin 7) ≤ Subgroup.closure {s, g₁ * s * g₁⁻¹, g₂ * s * g₂⁻¹} := by
  rcases cycleType_eq_replicate hs hs1 hsw with h | h
  · exact exists_alternatingGroup_le_closure_of_isConj
      (isConj_iff_cycleType_eq.2 (cycleType_two.trans h.symm))
      exists_alternatingGroup_le_closure_two
  · exact exists_alternatingGroup_le_closure_of_isConj
      (isConj_iff_cycleType_eq.2 (cycleType_three.trans h.symm))
      exists_alternatingGroup_le_closure_three

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
