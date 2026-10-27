module

public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.RankThree.PartTwo.Sec11

theorem three_dvd_sq_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have hq : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h => h3 (h ▸ dvd_zero 3)))
  omega

theorem padicValNat_cube_sq_sub_one {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) :
    padicValNat 3 ((q ^ 3) ^ 2 - 1) = padicValNat 3 (q ^ 2 - 1) + 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hx : ¬ 3 ∣ q ^ 2 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have h := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := q ^ 2) (y := 1) h1
    (three_dvd_sq_sub_one h3) hx (n := 3) (by norm_num)
  rw [one_pow, padicValNat_self] at h
  rw [← pow_mul, mul_comm 3 2, pow_mul]
  exact h

theorem three_adic_L2 {q : ℕ} (hq : 2 ≤ q) (h3 : ¬ 3 ∣ q) {A B : ℕ}
    (hA : A * Nat.gcd 2 (q ^ 3 - 1) = q ^ 3 * ((q ^ 3) ^ 2 - 1))
    (hB : B * Nat.gcd 2 (q - 1) = q * (q ^ 2 - 1)) :
    9 ∣ A ∧ B.factorization 3 < A.factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq3 : ¬ 3 ∣ q ^ 3 := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hq0 : 0 < q := by omega
  have h1 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have h1' : 1 < (q ^ 3) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by norm_num) (by omega))
  have hg : ∀ n : ℕ, padicValNat 3 (Nat.gcd 2 n) = 0 := by
    intro n
    have hd : Nat.gcd 2 n ∣ 2 := Nat.gcd_dvd_left 2 n
    have hle : Nat.gcd 2 n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hpos : 0 < Nat.gcd 2 n := Nat.gcd_pos_of_pos_left _ (by norm_num)
    interval_cases hgg : Nat.gcd 2 n <;> simp
  have hA0 : A ≠ 0 := by
    rintro rfl
    have : 0 < q ^ 3 * ((q ^ 3) ^ 2 - 1) := Nat.mul_pos (by positivity) (by omega)
    omega
  have hB0 : B ≠ 0 := by
    rintro rfl
    have : 0 < q * (q ^ 2 - 1) := Nat.mul_pos hq0 (by omega)
    omega
  have hgA0 : Nat.gcd 2 (q ^ 3 - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hgB0 : Nat.gcd 2 (q - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hvA : padicValNat 3 A = padicValNat 3 (q ^ 2 - 1) + 1 := by
    have h := congrArg (padicValNat 3) hA
    rw [padicValNat.mul hA0 hgA0, hg, add_zero,
      padicValNat.mul (by positivity) (by omega), padicValNat.eq_zero_of_not_dvd hq3, zero_add,
      padicValNat_cube_sq_sub_one hq h3] at h
    exact h
  have hvB : padicValNat 3 B = padicValNat 3 (q ^ 2 - 1) := by
    have h := congrArg (padicValNat 3) hB
    rw [padicValNat.mul hB0 hgB0, hg, add_zero,
      padicValNat.mul (by omega) (by omega), padicValNat.eq_zero_of_not_dvd h3, zero_add] at h
    exact h
  have hge : 1 ≤ padicValNat 3 (q ^ 2 - 1) := by
    exact one_le_padicValNat_of_dvd (by omega) (three_dvd_sq_sub_one h3)
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ padicValNat 3 A := by omega
    have := (padicValNat_dvd_iff_le (p := 3) (n := 2) hA0).2 h2
    simpa using this
  · rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three, hvA, hvB]
    omega

end CFSG.RankThree.PartTwo.Sec11
