module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.StandardType

open Equiv

theorem lt_two_pow_C {n : ℕ} (hn : 3 ≤ n) : n + 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem lt_two_pow_D {n : ℕ} (hn : 4 ≤ n) : n + 2 < 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have e : k + 1 - 1 = (k - 1) + 1 := by omega
    rw [e, pow_succ]; omega

theorem not_dvd_two_pow_mul_factorial_C {n : ℕ} (hn : 3 ≤ n) :
    ¬ 2 ^ n * n.factorial ∣ (n + 2).factorial := by
  intro h
  have h1 : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [h1] at h
  have h2 : 2 ^ n ∣ (n + 2) * (n + 1) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  have hlt := lt_two_pow_C hn
  rcases Nat.even_or_odd n with he | ho
  · have hodd : Odd (n + 1) := he.add_one
    have hc : Nat.Coprime (2 ^ n) (n + 1) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    have h3 : 2 ^ n ∣ n + 2 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  · have hodd : Odd (n + 2) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k + 1, by omega⟩
    have hc : Nat.Coprime (2 ^ n) (n + 2) :=
      Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
    have h3 : 2 ^ n ∣ n + 1 := hc.dvd_of_dvd_mul_left h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem not_dvd_two_pow_mul_factorial_D {n : ℕ} (hn : 4 ≤ n) :
    ¬ 2 ^ (n - 1) * n.factorial ∣ (n + 2).factorial := by
  intro h
  have h1 : (n + 2).factorial = (n + 2) * (n + 1) * n.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  rw [h1] at h
  have h2 : 2 ^ (n - 1) ∣ (n + 2) * (n + 1) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.factorial_pos n) h
  have hlt := lt_two_pow_D hn
  rcases Nat.even_or_odd n with he | ho
  · have hodd : Odd (n + 1) := he.add_one
    have hc : Nat.Coprime (2 ^ (n - 1)) (n + 1) :=
      Nat.Coprime.pow_left (n - 1) (Nat.coprime_two_left.mpr hodd)
    have h3 : 2 ^ (n - 1) ∣ n + 2 := hc.dvd_of_dvd_mul_right h2
    have := Nat.le_of_dvd (by omega) h3
    omega
  · have hodd : Odd (n + 2) := by
      obtain ⟨k, hk⟩ := ho
      exact ⟨k + 1, by omega⟩
    have hc : Nat.Coprime (2 ^ (n - 1)) (n + 2) :=
      Nat.Coprime.pow_left (n - 1) (Nat.coprime_two_left.mpr hodd)
    have h3 : 2 ^ (n - 1) ∣ n + 1 := hc.dvd_of_dvd_mul_left h2
    have := Nat.le_of_dvd (by omega) h3
    omega

theorem not_dvd_E : ¬ 51840 ∣ (8 : ℕ).factorial ∧ ¬ 2903040 ∣ (9 : ℕ).factorial ∧
    ¬ 696729600 ∣ (10 : ℕ).factorial ∧ ¬ 696729600 ∣ (11 : ℕ).factorial := by
  decide

theorem swap_commute_of_disjoint {α : Type*} [DecidableEq α] {a b c d : α}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (Equiv.swap a b) (Equiv.swap c d) := by
  refine Equiv.Perm.Disjoint.commute ?_
  intro z
  by_cases hz : z = a ∨ z = b
  · right
    rcases hz with rfl | rfl
    · exact Equiv.swap_apply_of_ne_of_ne hac had
    · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
  · left
    push Not at hz
    exact Equiv.swap_apply_of_ne_of_ne hz.1 hz.2

theorem orderOf_swap_dvd_six {α : Type*} [DecidableEq α] (x z : α) :
    orderOf (Equiv.swap x z) ∣ 6 :=
  (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Equiv.swap_mul_self x z)).trans
    (by norm_num)

theorem orderOf_swap_mul_swap_same_dvd {α : Type*} [DecidableEq α] [Fintype α] (x y z : α) :
    orderOf (Equiv.swap x y * Equiv.swap x z) ∣ 6 := by
  by_cases hxy : x = y
  · subst hxy
    have : Equiv.swap x x = 1 := Equiv.swap_self x
    rw [this, one_mul]
    exact orderOf_swap_dvd_six x z
  by_cases hxz : x = z
  · subst hxz
    have : Equiv.swap x x = 1 := Equiv.swap_self x
    rw [this, mul_one]
    exact orderOf_swap_dvd_six x y
  by_cases hyz : y = z
  · subst hyz
    rw [Equiv.swap_mul_self, orderOf_one]
    exact one_dvd _
  rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz).orderOf]
  norm_num

theorem orderOf_swap_mul_swap_dvd_six {α : Type*} [DecidableEq α] [Fintype α] (a b c d : α) :
    orderOf (Equiv.swap a b * Equiv.swap c d) ∣ 6 := by
  by_cases hac : a = c
  · subst hac
    exact orderOf_swap_mul_swap_same_dvd a b d
  by_cases had : a = d
  · subst had
    rw [Equiv.swap_comm c a]
    exact orderOf_swap_mul_swap_same_dvd a b c
  by_cases hbc : b = c
  · subst hbc
    rw [Equiv.swap_comm a b]
    exact orderOf_swap_mul_swap_same_dvd b a d
  by_cases hbd : b = d
  · subst hbd
    rw [Equiv.swap_comm a b, Equiv.swap_comm c b]
    exact orderOf_swap_mul_swap_same_dvd b a c
  have hcomm := swap_commute_of_disjoint hac had hbc hbd
  refine (orderOf_dvd_of_pow_eq_one ?_).trans (by norm_num : 2 ∣ 6)
  rw [hcomm.mul_pow, pow_two (Equiv.swap a b), pow_two (Equiv.swap c d), Equiv.swap_mul_self,
    Equiv.swap_mul_self, one_mul]

theorem not_four_dvd_orderOf_swap_mul_swap {α : Type*} [DecidableEq α] [Fintype α]
    (a b c d : α) : ¬ 4 ∣ orderOf (Equiv.swap a b * Equiv.swap c d) := fun h =>
  absurd (h.trans (orderOf_swap_mul_swap_dvd_six a b c d)) (by norm_num)

end CFSG.StandardType

end
