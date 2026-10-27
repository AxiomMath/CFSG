module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringUnitary

open CFSG.Assembly.RankThreeEven (projSU)

theorem two_pow_mul_eq_of_odd_mul {a b u v : ℕ} (hu : Odd u) (hv : Odd v)
    (h : 2 ^ a * u = 2 ^ b * v) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ b =>
      exfalso
      obtain ⟨i, hi⟩ := hu
      have h2 : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
      rw [h2, pow_zero, one_mul] at h
      have h' : u = 2 * (2 ^ b * v) := by linarith
      omega
  | succ a ih =>
    cases b with
    | zero =>
      exfalso
      obtain ⟨i, hi⟩ := hv
      have h2 : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
      rw [h2, pow_zero, one_mul] at h
      have h' : v = 2 * (2 ^ a * u) := by linarith
      omega
    | succ b =>
      have h2a : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
      have h2b : (2 : ℕ) ^ (b + 1) = 2 * 2 ^ b := by ring
      rw [h2a, h2b] at h
      have h' : 2 ^ a * u = 2 ^ b * v := by linarith
      have hab : a = b := ih (b := b) h'
      omega

theorem odd_pow_sub_one_of_two_dvd {x j : ℕ} (hx : 2 ∣ x) (hx0 : x ≠ 0) (hj : j ≠ 0) :
    Odd (x ^ j - 1) := by
  have h2 : 2 ∣ x ^ j := dvd_pow hx hj
  have hpos : 0 < x ^ j := pow_pos (Nat.pos_of_ne_zero hx0) j
  exact Nat.odd_iff.mpr (by omega)

theorem odd_pow_add_one_of_two_dvd {x j : ℕ} (hx : 2 ∣ x) (hj : j ≠ 0) :
    Odd (x ^ j + 1) := by
  have h2 : 2 ∣ x ^ j := dvd_pow hx hj
  exact Nat.odd_iff.mpr (by omega)

theorem false_of_arith_three_two {t s : ℕ} (hts : 2 * s ≤ t) (hs : 1 ≤ s)
    (h : t * (t ^ 2 - 1) * 3 = t * ((s - 1) * (t + 1))) : False := by
  have ht0 : 0 < t := by omega
  have h1 : (t ^ 2 - 1) * 3 = (s - 1) * (t + 1) := by
    apply Nat.eq_of_mul_eq_mul_left ht0
    calc t * ((t ^ 2 - 1) * 3) = t * (t ^ 2 - 1) * 3 := by ring
      _ = t * ((s - 1) * (t + 1)) := h
  have ht1 : 1 ≤ t ^ 2 := by
    have := pow_pos ht0 2
    omega
  have ht2 : (2 : ℕ) ≤ t := by omega
  zify [ht1, hs] at h1
  have hts' : (2 : ℤ) * s ≤ t := by exact_mod_cast hts
  have ht2' : (2 : ℤ) ≤ t := by exact_mod_cast ht2
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ t - 2 * s) (by linarith : (0 : ℤ) ≤ t + 1),
    mul_nonneg (by linarith : (0 : ℤ) ≤ t - 2) (by linarith : (0 : ℤ) ≤ t - 2)]

theorem card_projSU_three_two_ne_unitarySU_four {m k : ℕ} (hm : Odd m) (hk : 1 ≤ k) :
    Nat.card (projSU 3 2 m) ≠
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) := by
  intro hcard
  have hmain := CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_projSU_three_two_mul_three hm
  rw [hcard] at hmain
  have hm1 : m ≠ 0 := by
    obtain ⟨j, hj⟩ := hm
    omega
  have hk0 : (2 : ℕ) ^ k ≠ 0 := by positivity
  have hm0 : (2 : ℕ) ^ m ≠ 0 := by positivity
  have h2k : 2 ∣ (2 : ℕ) ^ k := dvd_pow_self 2 (by omega)
  have h2m : 2 ∣ (2 : ℕ) ^ m := dvd_pow_self 2 hm1
  have hX : Odd ((2 ^ k) ^ 2 - 1) := odd_pow_sub_one_of_two_dvd h2k hk0 (by norm_num)
  have hY : Odd ((2 ^ k) ^ 3 + 1) := odd_pow_add_one_of_two_dvd h2k (by norm_num)
  have hZ : Odd ((2 ^ k) ^ 4 - 1) := odd_pow_sub_one_of_two_dvd h2k hk0 (by norm_num)
  have hB : Odd (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3) :=
    ((hX.mul hY).mul hZ).mul (by decide)
  have hA : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    (odd_pow_sub_one_of_two_dvd h2m hm0 (by norm_num)).mul
      (odd_pow_add_one_of_two_dvd h2m (by norm_num))
  have e1 : (2 : ℕ) ^ (6 * k) = (2 ^ k) ^ 6 := by rw [← pow_mul, mul_comm]
  have e2 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
  have hkey : 2 ^ (6 * k) * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3) =
      2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
    have hstep : (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1) * 3)
        = (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) * ((2 ^ k) ^ 4 - 1)) * 3 := by
      ring
    rw [e1, e2, hstep]
    exact hmain
  have h6 := two_pow_mul_eq_of_odd_mul hB hA hkey
  obtain ⟨j, hj⟩ := hm
  omega

theorem card_projSU_three_two_ne_sl_two {m n : ℕ} (hm : Odd m) (hn : 1 ≤ n) :
    Nat.card (projSU 3 2 m) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro hcard
  have hmain := CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_projSU_three_two_mul_three hm
  rw [hcard] at hmain
  have hm1 : m ≠ 0 := by
    obtain ⟨j, hj⟩ := hm
    omega
  have hn0 : (2 : ℕ) ^ n ≠ 0 := by positivity
  have hm0 : (2 : ℕ) ^ m ≠ 0 := by positivity
  have h2n : 2 ∣ (2 : ℕ) ^ n := dvd_pow_self 2 (by omega)
  have h2m : 2 ∣ (2 : ℕ) ^ m := dvd_pow_self 2 hm1
  have hX : Odd ((2 ^ n) ^ 2 - 1) := odd_pow_sub_one_of_two_dvd h2n hn0 (by norm_num)
  have hC : Odd (3 * ((2 ^ n) ^ 2 - 1)) := (by decide : Odd (3 : ℕ)).mul hX
  have hA : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    (odd_pow_sub_one_of_two_dvd h2m hm0 (by norm_num)).mul
      (odd_pow_add_one_of_two_dvd h2m (by norm_num))
  have e2 : (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 := by rw [← pow_mul, mul_comm]
  have hkey : 2 ^ n * (3 * ((2 ^ n) ^ 2 - 1)) =
      2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
    have hstep : 2 ^ n * (3 * ((2 ^ n) ^ 2 - 1)) = 2 ^ n * ((2 ^ n) ^ 2 - 1) * 3 := by
      ring
    rw [e2, hstep]
    exact hmain
  have hnm : n = 3 * m := two_pow_mul_eq_of_odd_mul hC hA hkey
  subst hnm
  rw [← e2] at hmain
  have h2le : 2 ≤ (2 : ℕ) ^ m := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hts : 2 * (2 ^ m) ^ 2 ≤ 2 ^ (3 * m) := by
    rw [e2]
    nlinarith [Nat.mul_le_mul (le_refl ((2 ^ m) ^ 2)) h2le]
  have hs1 : 1 ≤ (2 ^ m) ^ 2 := by
    have := pow_pos (show (0 : ℕ) < 2 ^ m by positivity) 2
    omega
  exact false_of_arith_three_two hts hs1 hmain

end CFSG.RankThree.PartTwo.Sec4.HeringUnitary
