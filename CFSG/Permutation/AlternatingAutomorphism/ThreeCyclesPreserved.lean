module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG

namespace AlternatingAutomorphism

open Equiv Equiv.Perm Subgroup Nat

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem nat_card_centralizer_map {G : Type*} [Group G] (f : MulAut G) (g : G) :
    Nat.card (centralizer {f g}) = Nat.card (centralizer {g}) :=
  (Nat.card_congr <| f.toEquiv.subtypeEquiv fun x => by
    simp [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]).symm

private theorem exists_cycleType_eq_replicate {g : Perm α} (hg : orderOf g = 3) :
    ∃ k, 1 ≤ k ∧ 3 * k ≤ Fintype.card α ∧ g.cycleType = Multiset.replicate k 3 := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (hg ▸ Nat.prime_three)
  rw [hg] at hk
  refine ⟨k + 1, by omega, ?_, hk⟩
  have := sum_cycleType_le g
  simp only [hk, Multiset.sum_replicate, smul_eq_mul] at this
  omega

private theorem two_mul_nat_card_centralizer {g : alternatingGroup α} {k : ℕ} (hk : 1 ≤ k)
    (hg : (g : Perm α).cycleType = Multiset.replicate k 3) (hα : 5 ≤ Fintype.card α) :
    2 * Nat.card (centralizer {g}) = (Fintype.card α - 3 * k)! * 3 ^ k * k ! := by
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hC : ¬ centralizer {(g : Perm α)} ≤ alternatingGroup α := by
    rw [centralizer_le_alternating_iff, hg]
    rintro ⟨-, h₁, h₂⟩
    have := h₂ 3
    simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.count_replicate_self] at h₁ this
    omega
  have hindex : (alternatingGroup α).relIndex (centralizer {(g : Perm α)}) = 2 := by
    have := relIndex_dvd_index_of_normal (alternatingGroup α) (centralizer {(g : Perm α)})
    rw [alternatingGroup.index_eq_two] at this
    exact ((Nat.dvd_prime Nat.prime_two).mp this).resolve_left (mt relIndex_eq_one.mp hC)
  have hcard : Nat.card (centralizer {g}) =
      Nat.card ((alternatingGroup α).subgroupOf (centralizer {(g : Perm α)})) := by
    have : centralizer {g} = (centralizer {(g : Perm α)}).subgroupOf (alternatingGroup α) := by
      ext x
      simp [mem_subgroupOf, mem_centralizer_singleton_iff, Subtype.ext_iff]
    rw [this, ← card_map_of_injective (subtype_injective _), subgroupOf_map_subtype,
      ← card_map_of_injective (subtype_injective _), subgroupOf_map_subtype, inf_comm]
  rw [hcard, mul_comm, ← hindex, relIndex, card_mul_index, nat_card_centralizer, hg]
  simp [Multiset.toFinset_replicate, show k ≠ 0 by omega, mul_comm k 3]

private theorem pow_mul_factorial_mul_factorial_lt {j : ℕ} (hj : 1 ≤ j) :
    ∀ m, 4 ≤ m + 3 * j → 3 ^ j * (j + 1)! * m ! < (m + 3 * j)! := by
  induction j, hj using Nat.le_induction with
  | base =>
    intro m hm
    have e : (m + 3 * 1)! = (m + 3) * (m + 2) * (m + 1) * m ! := by
      simp only [mul_one, factorial_succ]
      ring
    have : 6 < (m + 3) * (m + 2) * (m + 1) :=
      calc 6 < 4 * 3 * 2 := by norm_num
        _ ≤ _ := by gcongr <;> omega
    rw [e, show 3 ^ 1 * (1 + 1)! = 6 from rfl]
    exact Nat.mul_lt_mul_of_pos_right this m.factorial_pos
  | succ j hj ih =>
    intro m hm
    rcases lt_or_ge (m + 3 * j) 4 with h | h
    · obtain rfl : j = 1 := by omega
      obtain rfl : m = 0 := by omega
      decide
    have h₂ : 3 * (j + 2) ≤ (m + 3 * j + 3) * (m + 3 * j + 2) * (m + 3 * j + 1) :=
      calc 3 * (j + 2) ≤ (m + 3 * j + 3) * 1 * 3 := by omega
        _ ≤ _ := by gcongr <;> omega
    have e₁ : (m + 3 * (j + 1))! =
        (m + 3 * j + 3) * (m + 3 * j + 2) * (m + 3 * j + 1) * (m + 3 * j)! := by
      rw [show m + 3 * (j + 1) = m + 3 * j + 2 + 1 by ring]
      simp only [factorial_succ]
      ring
    have e₂ : 3 ^ (j + 1) * (j + 1 + 1)! * m ! = 3 * (j + 2) * (3 ^ j * (j + 1)! * m !) := by
      rw [factorial_succ (j + 1), pow_succ]
      ring
    rw [e₁, e₂]
    calc _ < 3 * (j + 2) * (m + 3 * j)! := Nat.mul_lt_mul_of_pos_left (ih m h) (by positivity)
      _ ≤ _ := Nat.mul_le_mul_right _ h₂

private theorem factorial_mul_pow_mul_factorial_lt {n k : ℕ} (hn : 7 ≤ n) (hk : 2 ≤ k)
    (hkn : 3 * k ≤ n) : (n - 3 * k)! * 3 ^ k * k ! < (n - 3)! * 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have := pow_mul_factorial_mul_factorial_lt (j := j) (by omega) (n - 3 * (j + 1)) (by omega)
  rw [show n - 3 * (j + 1) + 3 * j = n - 3 by omega] at this
  rw [pow_succ]
  linarith

private theorem isThreeCycle_map (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α)
    (f : MulAut (alternatingGroup α)) {g : alternatingGroup α} (hg : (g : Perm α).IsThreeCycle) :
    (f g : Perm α).IsThreeCycle := by
  have h5 : 5 ≤ Fintype.card α := by omega
  have horder : orderOf (f g : Perm α) = 3 := by
    rw [orderOf_coe, MulEquiv.orderOf_eq, ← orderOf_coe, hg.orderOf]
  obtain ⟨k, hk, hkn, hfg⟩ := exists_cycleType_eq_replicate horder
  obtain rfl | hk : k = 1 ∨ 2 ≤ k := by omega
  · exact hfg
  · have h₁ := two_mul_nat_card_centralizer (by omega) hfg h5
    have h₂ := two_mul_nat_card_centralizer le_rfl hg.cycleType h5
    rw [nat_card_centralizer_map] at h₁
    have := factorial_mul_pow_mul_factorial_lt (by omega) hk hkn
    simp only [mul_one, pow_one, factorial_one] at h₂
    omega

theorem isThreeCycle_map_iff (hα : Fintype.card α = 5 ∨ 7 ≤ Fintype.card α)
    (f : MulAut (alternatingGroup α)) (g : alternatingGroup α) :
    (f g : Perm α).IsThreeCycle ↔ (g : Perm α).IsThreeCycle :=
  ⟨fun h => by simpa using isThreeCycle_map hα f.symm h, isThreeCycle_map hα f⟩

end AlternatingAutomorphism

end CFSG
