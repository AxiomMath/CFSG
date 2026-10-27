module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Arith
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne.KE.CTTw

open CFSG.RankThree.PartOne.KE.CTE6

theorem cast_pow_sub_one {q : ℕ} (hq : 1 ≤ q) (d : ℕ) :
    ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  ring

theorem not_dvd_pow_sub_one {p q m d : ℕ} (hord : orderOf (q : ZMod p) = m) (hmd : ¬ m ∣ d) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ d - 1 :=
  not_dvd_of_pow_ne_one (pow_ne_one_of_orderOf hord hmd) (Q := 1) (by ring)

theorem not_dvd_pow_add_one {p q m d : ℕ} (hord : orderOf (q : ZMod p) = m)
    (hmd : ¬ m ∣ 2 * d) : ¬ (p : ℤ) ∣ (q : ℤ) ^ d + 1 := by
  intro h
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  push_cast at h0
  apply hmd
  rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_mul', eq_neg_of_add_eq_zero_left h0, neg_one_sq]

theorem not_dvd_pow {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (d : ℕ) :
    ¬ (p : ℤ) ∣ (q : ℤ) ^ d :=
  fun h => hpq (Int.natCast_dvd_natCast.1 ((Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h))

theorem ordProj_eq_of_int_cofactor {p N n : ℕ} (hn : n ≠ 0) {R : ℤ}
    (hfac : (N : ℤ) = n * R) (hpR : ¬ (p : ℤ) ∣ R) : ordProj[p] N = ordProj[p] n := by
  have hR0 : R ≠ 0 := fun h => hpR (h ▸ dvd_zero _)
  have hN : N ≠ 0 := by
    rintro rfl
    have h0 : (n : ℤ) * R = 0 := by rw [← hfac]; simp
    rcases mul_eq_zero.1 h0 with h | h
    · exact hn (by exact_mod_cast h)
    · exact hR0 h
  exact ordProj_eq_of_int_factor hn hN hfac hpR

theorem ordProj_twisted_eight {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hord : orderOf (q : ZMod p) = 8) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p = p ^ ((q ^ 4 + 1) * (q ^ 2 - 1)).factorization p := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hn₀ : (q ^ 4 + 1) * (q ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h36 := not_dvd_pow hp hpq 36
  have h12 := not_dvd_pow_sub_one hord (show ¬ 8 ∣ 12 by norm_num)
  have h9 := not_dvd_pow_add_one hord (show ¬ 8 ∣ 2 * 9 by norm_num)
  have h4 := not_dvd_pow_sub_one hord (show ¬ 8 ∣ 4 by norm_num)
  have h6 := not_dvd_pow_sub_one hord (show ¬ 8 ∣ 6 by norm_num)
  have h5 := not_dvd_pow_add_one hord (show ¬ 8 ∣ 2 * 5 by norm_num)
  refine ordProj_eq_of_int_cofactor hn₀ (R := (q : ℤ) ^ 36 * ((q : ℤ) ^ 12 - 1) *
    ((q : ℤ) ^ 9 + 1) * ((q : ℤ) ^ 4 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 5 + 1)) ?_
    (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul
      (hpz.not_dvd_mul h36 h12) h9) h4) h6) h5)
  simp only [Nat.cast_mul, cast_pow_sub_one (by omega : 1 ≤ q), Nat.cast_add, Nat.cast_pow,
    Nat.cast_one]
  ring

theorem ordProj_twisted_twelve {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hord : orderOf (q : ZMod p) = 12) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p =
      p ^ ((q ^ 4 - q ^ 2 + 1) * (q ^ 2 - q + 1)).factorization p := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h21 : q ≤ q ^ 2 := by nlinarith
  have hn₀ : (q ^ 4 - q ^ 2 + 1) * (q ^ 2 - q + 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h36 := not_dvd_pow hp hpq 36
  have h4 := not_dvd_pow_sub_one hord (show ¬ 12 ∣ 4 by norm_num)
  have h3 : ¬ (p : ℤ) ∣ (q : ℤ) ^ 2 + q + 1 :=
    not_dvd_of_pow_ne_one (pow_ne_one_of_orderOf hord (show ¬ 12 ∣ 3 by norm_num))
      (Q := (q : ℤ) - 1) (by ring)
  have h9 := not_dvd_pow_add_one hord (show ¬ 12 ∣ 2 * 9 by norm_num)
  have h8 := not_dvd_pow_sub_one hord (show ¬ 12 ∣ 8 by norm_num)
  have h6 := not_dvd_pow_sub_one hord (show ¬ 12 ∣ 6 by norm_num)
  have h5 := not_dvd_pow_add_one hord (show ¬ 12 ∣ 2 * 5 by norm_num)
  have h2 := not_dvd_pow_sub_one hord (show ¬ 12 ∣ 2 by norm_num)
  refine ordProj_eq_of_int_cofactor hn₀ (R := (q : ℤ) ^ 36 * (((q : ℤ) ^ 4 - 1) *
    ((q : ℤ) ^ 2 + q + 1)) * ((q : ℤ) ^ 9 + 1) * ((q : ℤ) ^ 8 - 1) * ((q : ℤ) ^ 6 - 1) *
    ((q : ℤ) ^ 5 + 1) * ((q : ℤ) ^ 2 - 1)) ?_
    (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul
      (hpz.not_dvd_mul h36 (hpz.not_dvd_mul h4 h3)) h9) h8) h6) h5) h2)
  simp only [Nat.cast_mul, cast_pow_sub_one (by omega : 1 ≤ q), Nat.cast_add, Nat.cast_pow,
    Nat.cast_one, Nat.cast_sub h24, Nat.cast_sub h21]
  ring

theorem ordProj_twisted_eighteen {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hord : orderOf (q : ZMod p) = 18) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p = p ^ (q ^ 6 - q ^ 3 + 1).factorization p := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h36' : q ^ 3 ≤ q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hn₀ : q ^ 6 - q ^ 3 + 1 ≠ 0 := by omega
  have h36 := not_dvd_pow hp hpq 36
  have h12 := not_dvd_pow_sub_one hord (show ¬ 18 ∣ 12 by norm_num)
  have h3 := not_dvd_pow_add_one hord (show ¬ 18 ∣ 2 * 3 by norm_num)
  have h8 := not_dvd_pow_sub_one hord (show ¬ 18 ∣ 8 by norm_num)
  have h6 := not_dvd_pow_sub_one hord (show ¬ 18 ∣ 6 by norm_num)
  have h5 := not_dvd_pow_add_one hord (show ¬ 18 ∣ 2 * 5 by norm_num)
  have h2 := not_dvd_pow_sub_one hord (show ¬ 18 ∣ 2 by norm_num)
  refine ordProj_eq_of_int_cofactor hn₀ (R := (q : ℤ) ^ 36 * ((q : ℤ) ^ 12 - 1) *
    ((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 8 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 5 + 1) *
    ((q : ℤ) ^ 2 - 1)) ?_
    (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul
      (hpz.not_dvd_mul h36 h12) h3) h8) h6) h5) h2)
  simp only [Nat.cast_mul, cast_pow_sub_one (by omega : 1 ≤ q), Nat.cast_add, Nat.cast_pow,
    Nat.cast_one, Nat.cast_sub h36']
  ring

end CFSG.RankThree.PartOne.KE.CTTw
