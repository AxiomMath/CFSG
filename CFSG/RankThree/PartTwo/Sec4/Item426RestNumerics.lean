module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestInner

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

theorem restNumerics_A7 : RestNumerics 2520 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem restNumerics_M22 : RestNumerics 443520 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem twentySeven_dvd_sl {q : ℕ} (hq : q % 3 = 1) :
    27 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 1 := ⟨q / 3, by omega⟩
  have h1 : (3 * k + 1) ^ 2 - 1 = 3 * k * (3 * k + 2) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h2 : (3 * k + 1) ^ 3 - 1 = 9 * k * (3 * k ^ 2 + 3 * k + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [h1, h2]
  exact ⟨(3 * k + 1) ^ 3 * (k * (3 * k + 2)) * (k * (3 * k ^ 2 + 3 * k + 1)), by ring⟩

theorem twentySeven_dvd_su {q : ℕ} (hq : q % 3 = 2) :
    27 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  have h1 : (3 * k + 2) ^ 2 - 1 = 3 * (k + 1) * (3 * k + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have h2 : (3 * k + 2) ^ 3 + 1 = 9 * (3 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1) := by ring
  rw [h1, h2]
  exact ⟨(3 * k + 2) ^ 3 * ((k + 1) * (3 * k + 1)) * (3 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1),
    by ring⟩

theorem cube_dvd_of_dvd_three_pow_mul {q M' : ℕ} (hq : ¬ 3 ∣ q) (a : ℕ)
    (h : q ^ 3 ∣ 3 ^ a * M') : q ^ 3 ∣ M' := by
  have hc : Nat.Coprime (q ^ 3) (3 ^ a) :=
    Nat.Coprime.pow 3 a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hq).symm
  exact hc.dvd_of_dvd_mul_left h

theorem restNumerics_of_card {q N : ℕ} {π : Bool} (hq2 : 2 < q) (hmod : ModThree π q)
    (hN : N * 3 = q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1)) : RestNumerics N := by
  have hq3 : q % 3 = 1 ∨ q % 3 = 2 := by
    cases π
    · exact Or.inr hmod
    · exact Or.inl hmod
  have hq3' : ¬ 3 ∣ q := by omega
  have hq4 : 4 ≤ q := by omega
  have hcube : q ^ 3 ∣ N := by
    have hc : Nat.Coprime (q ^ 3) 3 :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hq3').symm
    exact hc.dvd_of_dvd_mul_right ⟨(q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1), by
      rw [hN]; ring⟩
  have hlow : 60480 ≤ N * 3 := by
    rw [hN]
    have h1 : 64 ≤ q ^ 3 := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    have h2 : 15 ≤ q ^ 2 - 1 := by
      have : 16 ≤ q ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have h3 : 63 ≤ cond π (q ^ 3 - 1) (q ^ 3 + 1) := by
      cases π <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega
    calc 60480 = 64 * 15 * 63 := by norm_num
      _ ≤ q ^ 3 * (q ^ 2 - 1) * cond π (q ^ 3 - 1) (q ^ 3 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have h4 : q = 4 → N = 20160 := by
    intro hq
    subst hq
    cases π
    · change 4 % 3 = 2 at hmod
      omega
    · simp only [Bool.cond_true] at hN
      omega
  have hnot : ∀ (a M' : ℕ), N ∣ 3 ^ a * M' → q ^ 3 ∣ M' := fun a M' hd =>
    cube_dvd_of_dvd_three_pow_mul hq3' a (hcube.trans hd)
  refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h27 : 27 ∣ N * 3 := by
      rw [hN]
      cases π
      · exact twentySeven_dvd_su hmod
      · exact twentySeven_dvd_sl hmod
    omega
  · intro hd
    have hc := hnot 6 40 (by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) hc
    have : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    omega
  · intro hd
    have hc := hnot 5 4 (by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) hc
    have : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    omega
  · intro hd
    have hc := hnot 4 40 (by norm_num; exact hd)
    have := Nat.le_of_dvd (by norm_num) hc
    have : 4 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
    omega
  · intro hd
    have hc := hnot 6 896 (by norm_num; exact hd)
    have hle := Nat.le_of_dvd (by norm_num) hc
    have hq9 : q ≤ 9 := by
      by_contra hq
      have : 10 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    interval_cases q <;> first | omega | (rw [h4 rfl] at hd; norm_num at hd)
  · intro hd
    have hc := hnot 6 5824 (by norm_num; exact hd)
    have hle := Nat.le_of_dvd (by norm_num) hc
    have hq18 : q ≤ 18 := by
      by_contra hq
      have : 19 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    interval_cases q <;> first | omega | (rw [h4 rfl] at hd; norm_num at hd)

theorem big_of_ge_eight {x : ℕ} (hx : 8 ≤ x) :
    16482816 ≤ x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := by
  have h1 : 512 ≤ x ^ 3 := by
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
  have h2 : 63 ≤ x ^ 2 - 1 := by
    have : 64 ≤ x ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
    omega
  have h3 : 511 ≤ x ^ 3 - 1 := by omega
  calc 16482816 = 512 * 63 * 511 := by norm_num
    _ ≤ x ^ 3 * (x ^ 2 - 1) * (x ^ 3 - 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem card_sl_two_pow_ne {j : ℕ} (hj : 1 ≤ j) :
    (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 - 1) ≠ 7560 ∧
      (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 - 1) ≠ 1330560 := by
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j <;> norm_num
  · have h8 : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
    have := big_of_ge_eight h8
    omega

theorem card_su_two_pow_ne {j : ℕ} (hj : 2 ≤ j) :
    (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1) ≠ 7560 ∧
      (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1) ≠ 1330560 := by
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    norm_num
  · have h8 : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
    have h1 := big_of_ge_eight h8
    have h2 : (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 - 1) ≤
        (2 ^ j) ^ 3 * ((2 ^ j) ^ 2 - 1) * ((2 ^ j) ^ 3 + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
