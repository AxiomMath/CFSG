module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.S146zY.SzNoFive

theorem two_pow_odd_mod_five (a : ℕ) :
    2 ^ (2 * a + 1) % 5 = 2 ∨ 2 ^ (2 * a + 1) % 5 = 3 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    have h : 2 ^ (2 * (n + 1) + 1) = 2 ^ (2 * n + 1) * 4 := by ring
    rw [h]
    generalize 2 ^ (2 * n + 1) = x at ih ⊢
    omega

theorem not_five_dvd_sq_mul_pred (a : ℕ) :
    ¬ 5 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  have h := two_pow_odd_mod_five a
  generalize 2 ^ (2 * a + 1) = q at h ⊢
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 hd with h1 | h1
  · have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h1)
    omega
  · omega

theorem sq_add_one_ne_five_pow (a j : ℕ) (ha : 1 ≤ a) : (2 ^ (2 * a + 1)) ^ 2 + 1 ≠ 5 ^ j := by
  intro h
  have h8 : (2 ^ (2 * a + 1)) ^ 2 % 8 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    have : (2 ^ (2 * a + 1)) ^ 2 = 2 ^ ((2 * a + 1) * 2) := by rw [← pow_mul]
    rw [this]
    exact (pow_dvd_pow 2 (by omega : 3 ≤ (2 * a + 1) * 2))
  have h3 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    have : (2 ^ (2 * a + 1)) ^ 2 = 4 ^ (2 * a + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, Nat.pow_mod]; norm_num
  have h25_8 : ∀ i : ℕ, 25 ^ i % 8 = 1 := fun i => by
    rw [Nat.pow_mod]; norm_num
  have h25_3 : ∀ i : ℕ, 25 ^ i % 3 = 1 := fun i => by
    rw [Nat.pow_mod]; norm_num
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · have e : 5 ^ (2 * i) = 25 ^ i := by rw [pow_mul]; norm_num
    rw [e] at h
    have := h25_3 i
    omega
  · have e : 5 ^ (2 * i + 1) = 25 ^ i * 5 := by rw [pow_succ, pow_mul]; norm_num
    rw [e] at h
    have := h25_8 i
    omega

end CFSG.Quasithin.S146zY.SzNoFive
