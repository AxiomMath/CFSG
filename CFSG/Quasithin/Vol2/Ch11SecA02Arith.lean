module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.DesarguesianPlanes.JordanDerivation

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

theorem dvd_of_two_pow_sub_one_dvd {a b : ℕ} (h : 2 ^ a - 1 ∣ 2 ^ b - 1) : a ∣ b := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 a b
  rw [Nat.gcd_eq_left h] at hg
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ Nat.gcd a b := Nat.one_le_two_pow
  have h3 : 2 ^ a = 2 ^ Nat.gcd a b := by omega
  have h4 : a = Nat.gcd a b := Nat.pow_right_injective le_rfl h3
  rw [h4]
  exact Nat.gcd_dvd_right a b

abbrev oSL2 (m : ℕ) : ℕ := 2 ^ (2 * m) - 1

abbrev oSL3 (n : ℕ) : ℕ := (2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)

abbrev oSp4 (n : ℕ) : ℕ := (2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)

abbrev oG2 (n : ℕ) : ℕ := (2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)

theorem two_pow_two_mul_sub_one (a : ℕ) : 2 ^ (2 * a) - 1 = (2 ^ a - 1) * (2 ^ a + 1) := by
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rw [pow_mul', sq]
  zify [h1, Nat.one_le_two_pow (n := 2 * a), show 1 ≤ 2 ^ a * 2 ^ a from Nat.one_le_iff_ne_zero.mpr
    (by positivity)]
  ring

theorem two_pow_sub_one_pos {a : ℕ} (ha : 1 ≤ a) : 0 < 2 ^ a - 1 := by
  have : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  omega

theorem two_pow_sub_one_lt {a b : ℕ} (hab : a < b) : 2 ^ a - 1 < 2 ^ b - 1 := by
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  omega

theorem not_mul_dvd_mul_of_lt {x y z : ℕ} (hx : 0 < x) (hz : 0 < z) (hzy : z < y) :
    ¬ x * y ∣ x * z := by
  intro h
  have := Nat.le_of_dvd hz (Nat.dvd_of_mul_dvd_mul_left hx h)
  omega

theorem not_dvd_oSL2_oSL3 {n : ℕ} (hn : 1 ≤ n) : ¬ oSL2 (3 * n) ∣ oSL3 n := by
  rw [oSL2, oSL3, two_pow_two_mul_sub_one]
  refine not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega)) ?_
  have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2 * n ≤ 3 * n by omega)
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le this)

theorem not_dvd_oSL2_oSp4 {n : ℕ} (hn : 1 ≤ n) : ¬ oSL2 (4 * n) ∣ oSp4 n := by
  rw [oSL2, oSp4, two_pow_two_mul_sub_one, mul_comm (2 ^ (2 * n) - 1)]
  refine not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega)) ?_
  have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2 * n ≤ 4 * n by omega)
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le this)

theorem not_dvd_oSL2_oG2 {n : ℕ} (hn : 1 ≤ n) : ¬ oSL2 (6 * n) ∣ oG2 n := by
  rw [oSL2, oG2, two_pow_two_mul_sub_one]
  refine not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega)) ?_
  have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2 * n ≤ 6 * n by omega)
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le this)

theorem not_dvd_oSL3_oSp4 {k : ℕ} (hk : 1 ≤ k) : ¬ oSL3 (4 * k) ∣ oSp4 (3 * k) := by
  rw [oSL3, oSp4, show 3 * (4 * k) = 4 * (3 * k) by ring, show 2 * (4 * k) = 8 * k by ring,
    show 2 * (3 * k) = 6 * k by ring, mul_comm (2 ^ (6 * k) - 1)]
  exact not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega))
    (two_pow_sub_one_lt (by omega))

theorem not_dvd_oSL3_oG2 {n : ℕ} (hn : 1 ≤ n) : ¬ oSL3 (2 * n) ∣ oG2 n := by
  rw [oSL3, oG2, show 3 * (2 * n) = 6 * n by ring, show 2 * (2 * n) = 4 * n by ring]
  exact not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega))
    (two_pow_sub_one_lt (by omega))

theorem not_dvd_oSp4_oSL3 {k : ℕ} (hk : 1 ≤ k) : ¬ oSp4 (3 * k) ∣ oSL3 (4 * k) := by
  rw [oSp4, oSL3, show 3 * (4 * k) = 4 * (3 * k) by ring, show 2 * (4 * k) = 8 * k by ring,
    show 2 * (3 * k) = 6 * k by ring, mul_comm (2 ^ (6 * k) - 1)]
  intro h
  have h1 := Nat.dvd_of_mul_dvd_mul_left (two_pow_sub_one_pos (by omega)) h
  have h2 := dvd_of_two_pow_sub_one_dvd h1
  have h3 : 6 * k ∣ 2 * k := by
    have := Nat.dvd_sub h2 (dvd_refl (6 * k))
    rwa [show 8 * k - 6 * k = 2 * k by omega] at this
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem not_dvd_oSp4_oG2 {k : ℕ} (hk : 1 ≤ k) : ¬ oSp4 (3 * k) ∣ oG2 (2 * k) := by
  rw [oSp4, oG2, show 4 * (3 * k) = 6 * (2 * k) by ring, show 2 * (3 * k) = 6 * k by ring,
    show 2 * (2 * k) = 4 * k by ring, mul_comm (2 ^ (6 * k) - 1)]
  exact not_mul_dvd_mul_of_lt (two_pow_sub_one_pos (by omega)) (two_pow_sub_one_pos (by omega))
    (two_pow_sub_one_lt (by omega))

theorem not_dvd_oG2_oSp4 {k : ℕ} (hk : 1 ≤ k) : ¬ oG2 (2 * k) ∣ oSp4 (3 * k) := by
  rw [oG2, oSp4, show 6 * (2 * k) = 4 * (3 * k) by ring, show 2 * (2 * k) = 4 * k by ring,
    show 2 * (3 * k) = 6 * k by ring, mul_comm (2 ^ (6 * k) - 1)]
  intro h
  have h1 := Nat.dvd_of_mul_dvd_mul_left (two_pow_sub_one_pos (by omega)) h
  have h2 := dvd_of_two_pow_sub_one_dvd h1
  have h3 : 4 * k ∣ 2 * k := by
    have := Nat.dvd_sub h2 (dvd_refl (4 * k))
    rwa [show 6 * k - 4 * k = 2 * k by omega] at this
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem oSL3_two_mul (m : ℕ) : oSL3 (2 * m) = (2 ^ (2 * m) + 1) * oG2 m := by
  rw [oSL3, oG2, show 3 * (2 * m) = 6 * m by ring, show 2 * (2 * m) = 2 * (2 * m) by ring,
    two_pow_two_mul_sub_one (2 * m)]
  ring

end CFSG.Quasithin.Vol2.Ch11.SecA
