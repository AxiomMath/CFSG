module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ASVolI.ChH

namespace ElemAb2Orbits

private theorem exists_counts (s : Multiset ℕ) (hs : ∀ a ∈ s, a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8) :
    ∃ a b c d : ℕ, s = Multiset.replicate a 1 + Multiset.replicate b 2 +
      Multiset.replicate c 4 + Multiset.replicate d 8 := by
  refine ⟨s.count 1, s.count 2, s.count 4, s.count 8, Multiset.ext.mpr fun x => ?_⟩
  simp only [Multiset.count_add, Multiset.count_replicate]
  by_cases h1 : x = 1
  · subst h1; simp
  by_cases h2 : x = 2
  · subst h2; simp
  by_cases h4 : x = 4
  · subst h4; simp
  by_cases h8 : x = 8
  · subst h8; simp
  have hx : x ∉ s := fun h => by rcases hs x h with h | h | h | h <;> contradiction
  rw [Multiset.count_eq_zero.mpr hx]
  simp [Ne.symm h1, Ne.symm h2, Ne.symm h4, Ne.symm h8]

private theorem sum_counts (a b c d : ℕ) :
    (Multiset.replicate a 1 + Multiset.replicate b 2 + Multiset.replicate c 4 +
      Multiset.replicate d 8).sum = a + 2 * b + 4 * c + 8 * d := by
  simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  ring

private theorem prod_counts (a b c d : ℕ) :
    (Multiset.replicate a 1 + Multiset.replicate b 2 + Multiset.replicate c 4 +
      Multiset.replicate d 8).prod = 2 ^ b * 4 ^ c * 8 ^ d := by
  simp only [Multiset.prod_add, Multiset.prod_replicate, one_pow]
  ring

theorem multiset_prod_le_sixteen {s : Multiset ℕ}
    (hs : ∀ a ∈ s, a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8) (hsum : s.sum = 8) : s.prod ≤ 16 := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_counts s hs
  rw [sum_counts] at hsum
  rw [prod_counts]
  have hd : d ≤ 1 := by omega
  have hc : c ≤ 2 := by omega
  have hb : b ≤ 4 := by omega
  interval_cases d <;> interval_cases c <;> interval_cases b <;>
    first | (exfalso; omega) | norm_num

theorem multiset_eq_of_sixteen_le_prod {s : Multiset ℕ}
    (hs : ∀ a ∈ s, a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8) (hsum : s.sum = 8) (hprod : 16 ≤ s.prod) :
    s = {4, 4} ∨ s = {4, 2, 2} ∨ s = {2, 2, 2, 2} := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_counts s hs
  rw [sum_counts] at hsum
  rw [prod_counts] at hprod
  have hd : d ≤ 1 := by omega
  have hc : c ≤ 2 := by omega
  have hb : b ≤ 4 := by omega
  interval_cases d <;> interval_cases c <;> interval_cases b <;>
    first
    | (exfalso; omega)
    | (exfalso; norm_num at hprod; done)
    | (obtain rfl : a = 0 := by omega
       decide)

end ElemAb2Orbits

end CFSG.ASVolI.ChH
