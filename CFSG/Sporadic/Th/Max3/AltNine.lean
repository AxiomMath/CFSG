module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Sporadic.Th.Max3

open Equiv Equiv.Perm

@[expose] def altRep2 : Perm (Fin 9) := swap 0 1 * swap 2 3

@[expose] def altRep4 : Perm (Fin 9) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

theorem cycleType_altRep2 : altRep2.cycleType = {2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 9) 1) (swap 2 3) := by
    intro x
    fin_cases x <;> simp [swap_apply_def]
  rw [altRep2, Equiv.Perm.Disjoint.cycleType_mul hd, (isCycle_swap (by decide)).cycleType,
    (isCycle_swap (by decide)).cycleType, card_support_swap (by decide),
    card_support_swap (by decide)]
  rfl

theorem cycleType_altRep4 : altRep4.cycleType = {2, 2, 2, 2} := by
  have h1 : Equiv.Perm.Disjoint (swap (0 : Fin 9) 1) (swap 2 3) := by
    intro x; fin_cases x <;> simp [swap_apply_def]
  have h2 : Equiv.Perm.Disjoint (swap (0 : Fin 9) 1 * swap 2 3) (swap 4 5) := by
    intro x; fin_cases x <;> simp [swap_apply_def]
  have h3 : Equiv.Perm.Disjoint (swap (0 : Fin 9) 1 * swap 2 3 * swap 4 5) (swap 6 7) := by
    intro x; fin_cases x <;> simp [swap_apply_def]
  rw [altRep4, Equiv.Perm.Disjoint.cycleType_mul h3, Equiv.Perm.Disjoint.cycleType_mul h2,
    Equiv.Perm.Disjoint.cycleType_mul h1]
  simp only [(isCycle_swap (by decide : (0 : Fin 9) ≠ 1)).cycleType,
    (isCycle_swap (by decide : (2 : Fin 9) ≠ 3)).cycleType,
    (isCycle_swap (by decide : (4 : Fin 9) ≠ 5)).cycleType,
    (isCycle_swap (by decide : (6 : Fin 9) ≠ 7)).cycleType,
    card_support_swap (by decide : (0 : Fin 9) ≠ 1),
    card_support_swap (by decide : (2 : Fin 9) ≠ 3),
    card_support_swap (by decide : (4 : Fin 9) ≠ 5),
    card_support_swap (by decide : (6 : Fin 9) ≠ 7)]
  rfl

theorem swap_mul_altRep2 : swap (0 : Fin 9) 1 * altRep2 = altRep2 * swap 0 1 := by decide

theorem swap_mul_altRep4 : swap (0 : Fin 9) 1 * altRep4 = altRep4 * swap 0 1 := by decide

theorem sign_altRep2 : sign altRep2 = 1 := by decide

theorem sign_altRep4 : sign altRep4 = 1 := by decide

theorem cycleType_of_orderOf_eq_two {σ : Perm (Fin 9)} (hσ : orderOf σ = 2) (hs : sign σ = 1) :
    σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2, 2} := by
  have h2 : ∀ m ∈ σ.cycleType, m = 2 := by
    intro m hm
    have hd := dvd_of_mem_cycleType hm
    rw [hσ] at hd
    have hle := two_le_of_mem_cycleType hm
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card σ.cycleType = k := ⟨_, rfl⟩
  have hrep : σ.cycleType = Multiset.replicate k 2 := by
    rw [← hk]
    exact Multiset.eq_replicate.mpr ⟨rfl, h2⟩
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 2 * k ≤ 9 := by
    rw [← hsum, sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hne : k ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_eq_zero, cycleType_eq_zero] at hk
    rw [hk, orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have heven : Even k := by
    have := sign_of_cycleType σ
    rw [hs, hsum, hk] at this
    rcases Nat.even_or_odd k with he | ho
    · exact he
    · exfalso
      have hodd : Odd (2 * k + k) := by
        obtain ⟨j, hj⟩ := ho
        exact ⟨3 * j + 1, by omega⟩
      rw [hodd.neg_one_pow] at this
      exact absurd this (by decide)
  obtain ⟨j, hj⟩ := heven
  have hk' : k = 2 ∨ k = 4 := by omega
  rcases hk' with h | h
  · left
    rw [hrep, h]
    rfl
  · right
    rw [hrep, h]
    rfl

theorem exists_conj_eq_of_orderOf_eq_two {σ : Perm (Fin 9)} (hσA : σ ∈ alternatingGroup (Fin 9))
    (hσ : orderOf σ = 2) :
    ∃ g ∈ alternatingGroup (Fin 9), g * σ * g⁻¹ = altRep2 ∨ g * σ * g⁻¹ = altRep4 := by
  have hs : sign σ = 1 := (mem_alternatingGroup).mp hσA
  have key : ∀ r : Perm (Fin 9), sign r = 1 → swap (0 : Fin 9) 1 * r = r * swap 0 1 →
      σ.cycleType = r.cycleType → ∃ g ∈ alternatingGroup (Fin 9), g * σ * g⁻¹ = r := by
    intro r _ hcomm hct
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr hct)
    by_cases hg1 : sign g = 1
    · exact ⟨g, (mem_alternatingGroup).mpr hg1, hg⟩
    · refine ⟨swap 0 1 * g, ?_, ?_⟩
      · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide)]
        rcases Int.units_eq_one_or (sign g) with h | h
        · exact absurd h hg1
        · rw [h]
          decide
      · have hinv : (swap (0 : Fin 9) 1)⁻¹ = swap 0 1 := swap_inv 0 1
        calc swap 0 1 * g * σ * (swap 0 1 * g)⁻¹ = swap 0 1 * (g * σ * g⁻¹) * (swap 0 1)⁻¹ := by
              group
          _ = swap 0 1 * r * swap 0 1 := by rw [hg, hinv]
          _ = r := by rw [hcomm, mul_assoc, swap_mul_self, mul_one]
  rcases cycleType_of_orderOf_eq_two hσ hs with h | h
  · obtain ⟨g, hgA, hg⟩ :=
      key altRep2 sign_altRep2 swap_mul_altRep2 (h.trans cycleType_altRep2.symm)
    exact ⟨g, hgA, Or.inl hg⟩
  · obtain ⟨g, hgA, hg⟩ :=
      key altRep4 sign_altRep4 swap_mul_altRep4 (h.trans cycleType_altRep4.symm)
    exact ⟨g, hgA, Or.inr hg⟩

end CFSG.Sporadic.Th.Max3
