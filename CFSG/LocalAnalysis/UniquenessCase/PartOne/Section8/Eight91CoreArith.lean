module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core

open CFSG.Open

theorem ordTrialityD4_two_pow_eq (n : ℕ) :
    ordTrialityD4 (2 ^ n) = 2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) * (2 ^ (6 * n) - 1) *
      (2 ^ (2 * n) - 1) := by
  simp only [ordTrialityD4, ← pow_mul, Nat.mul_comm n]

private theorem pow_two_sub_one_eq (q : ℕ) (hq : 1 ≤ q) :
    q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have h : 1 ≤ q ^ 2 := one_le_pow₀ hq
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h, Nat.cast_sub hq]
  push_cast
  ring

private theorem pow_three_sub_one_eq (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
  have h : 1 ≤ q ^ 3 := one_le_pow₀ hq
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h, Nat.cast_sub hq]
  push_cast
  ring

private theorem pow_three_add_one_eq (q : ℕ) (hq : 1 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have h : q ≤ q ^ 2 := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h]
  push_cast
  ring

private theorem pow_two_sub_self_eq (q : ℕ) (hq : 1 ≤ q) :
    q ^ 2 - q = q * (q - 1) := by
  have h : q ≤ q ^ 2 := by nlinarith
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h, Nat.cast_sub hq]
  push_cast
  ring

private theorem pow_four_add_pow_two_add_one_mul (q : ℕ) (hq : q ^ 2 ≤ q ^ 4) :
    (q ^ 4 + q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) = q ^ 8 + q ^ 4 + 1 := by
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub hq]
  push_cast
  ring

private theorem pow_two_sub_one_mul (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) = q ^ 6 - 1 := by
  have h2 : 1 ≤ q ^ 2 := by have := pow_pos (by omega : 0 < q) 2; omega
  have h6 : 1 ≤ q ^ 6 := by have := pow_pos (by omega : 0 < q) 6; omega
  apply Nat.cast_injective (R := ℤ)
  push_cast
  rw [Nat.cast_sub h2, Nat.cast_sub h6]
  push_cast
  ring

theorem dvd_or_dvd_of_dvd_ordTrialityD4 {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ∣ ordTrialityD4 (2 ^ n)) : p ∣ 2 ^ (6 * n) - 1 ∨ p ∣ 2 ^ (4 * n) - 2 ^ (2 * n) + 1 := by
  by_cases hn : n = 0
  · subst hn; left; norm_num
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  let q := 2 ^ n
  have hq2le : 2 ≤ q := by
    dsimp only [q]
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) hn1
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ^ 2 = 2 ^ (2 * n) := by
    dsimp only [q]; rw [← pow_mul]; congr 1; ring
  have hq4 : q ^ 4 = 2 ^ (4 * n) := by
    dsimp only [q]; rw [← pow_mul]; congr 1; ring
  have hq6 : q ^ 6 = 2 ^ (6 * n) := by
    dsimp only [q]; rw [← pow_mul]; congr 1; ring
  have hq8 : q ^ 8 = 2 ^ (8 * n) := by
    dsimp only [q]; rw [← pow_mul]; congr 1; ring
  have hq12 : q ^ 12 = 2 ^ (12 * n) := by
    dsimp only [q]; rw [← pow_mul]; congr 1; ring
  rw [ordTrialityD4_two_pow_eq] at h
  rw [← hq12, ← hq8, ← hq4, ← hq6, ← hq2] at h
  have hpq : ¬ p ∣ q ^ 12 := by
    intro hd
    dsimp only [q] at hd
    have h1 : p ∣ 2 ^ n := hp.dvd_of_dvd_pow hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h1
    have := Nat.le_of_dvd (by norm_num : 0 < 2) h2
    omega
  have hAid : q ^ 8 + q ^ 4 + 1 = (q ^ 4 + q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) :=
    (pow_four_add_pow_two_add_one_mul q
      (pow_le_pow_right₀ hq1 (by norm_num : 2 ≤ 4))).symm
  have hBid : (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) = q ^ 6 - 1 :=
    pow_two_sub_one_mul q hq1
  have hCB : q ^ 2 - 1 ∣ q ^ 6 - 1 := ⟨_, hBid.symm⟩
  rcases (hp.dvd_mul).mp h with hAB | hC
  · rcases (hp.dvd_mul).mp hAB with h12A | hB
    · rcases (hp.dvd_mul).mp h12A with h12 | hA
      · exact absurd h12 hpq
      · have hDE : p ∣ (q ^ 4 + q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) := by
          rwa [hAid] at hA
        have hmul : p ∣ ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1)) * (q ^ 2 - 1) :=
          dvd_mul_of_dvd_left hDE _
        have heq : ((q ^ 4 + q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1)) * (q ^ 2 - 1) =
            (q ^ 4 - q ^ 2 + 1) * (q ^ 6 - 1) := by
          rw [mul_assoc, mul_comm (q ^ 4 - q ^ 2 + 1) (q ^ 2 - 1), ← mul_assoc,
            mul_comm (q ^ 4 + q ^ 2 + 1) (q ^ 2 - 1), hBid, mul_comm]
        rw [heq] at hmul
        rcases (hp.dvd_mul).mp hmul with hE | hB
        · right
          rwa [hq4, hq2] at hE
        · left
          rwa [hq6] at hB
    · left
      rwa [hq6] at hB
  · left
    rw [hq6] at hCB
    exact dvd_trans hC hCB

theorem factorization_two_ordTrialityD4_two_pow {n : ℕ} (hn : 1 ≤ n) :
    (ordTrialityD4 (2 ^ n)).factorization 2 = 12 * n := by
  rw [ordTrialityD4_two_pow_eq]
  have h8even : Even (2 ^ (8 * n)) := by
    rw [Nat.even_pow]
    exact ⟨⟨1, by norm_num⟩, by omega⟩
  have h4even : Even (2 ^ (4 * n)) := by
    rw [Nat.even_pow]
    exact ⟨⟨1, by norm_num⟩, by omega⟩
  have h6even : Even (2 ^ (6 * n)) := by
    rw [Nat.even_pow]
    exact ⟨⟨1, by norm_num⟩, by omega⟩
  have h2even : Even (2 ^ (2 * n)) := by
    rw [Nat.even_pow]
    exact ⟨⟨1, by norm_num⟩, by omega⟩
  have hAodd : Odd (2 ^ (8 * n) + 2 ^ (4 * n) + 1) :=
    Even.add_odd (Even.add h8even h4even) ⟨0, by norm_num⟩
  have hBodd : Odd (2 ^ (6 * n) - 1) :=
    Nat.Even.sub_odd (by have := pow_pos (by norm_num : 0 < 2) (6 * n); omega)
      h6even ⟨0, by norm_num⟩
  have hCodd : Odd (2 ^ (2 * n) - 1) :=
    Nat.Even.sub_odd (by have := pow_pos (by norm_num : 0 < 2) (2 * n); omega)
      h2even ⟨0, by norm_num⟩
  have hAn2 : (2 ^ (8 * n) + 2 ^ (4 * n) + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hAodd.not_two_dvd_nat
  have hBn2 : (2 ^ (6 * n) - 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hBodd.not_two_dvd_nat
  have hCn2 : (2 ^ (2 * n) - 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hCodd.not_two_dvd_nat
  have h12ne : 2 ^ (12 * n) ≠ 0 := by positivity
  have hAne : 2 ^ (8 * n) + 2 ^ (4 * n) + 1 ≠ 0 := by positivity
  have hBne : 2 ^ (6 * n) - 1 ≠ 0 := by
    have h : 2 ≤ 2 ^ (6 * n) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 1 ≤ 6 * n)
    omega
  have hCne : 2 ^ (2 * n) - 1 ≠ 0 := by
    have h : 2 ≤ 2 ^ (2 * n) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 1 ≤ 2 * n)
    omega
  rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.mul_ne_zero h12ne hAne) hBne) hCne]
  rw [Nat.factorization_mul (Nat.mul_ne_zero h12ne hAne) hBne]
  rw [Nat.factorization_mul h12ne hAne]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_pow_self (by norm_num : Nat.Prime 2), hAn2, hBn2, hCn2]
  omega

private theorem two_pow_twelve_dvd_ordTrialityD4 (n : ℕ) :
    2 ^ (12 * n) ∣ ordTrialityD4 (2 ^ n) := by
  rw [ordTrialityD4_two_pow_eq]
  refine ⟨(2 ^ (8 * n) + 2 ^ (4 * n) + 1) * (2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1), ?_⟩
  ring

private theorem two_pow_twelve_dvd_sl3_part {n r : ℕ} (hr : Odd r) (hr3 : 3 ≤ r)
    (h : 2 ^ (12 * n) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1)) :
    2 ^ (12 * n) ∣ (r - 1) ^ 2 * (r + 1) := by
  have hr1 : 1 ≤ r := by omega
  have h2 : r ^ 2 - 1 = (r - 1) * (r + 1) := pow_two_sub_one_eq r hr1
  have h3 : r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) := pow_three_sub_one_eq r hr1
  have hcop_r : Nat.Coprime (2 ^ (12 * n)) (r ^ 3) :=
    hr.coprime_two_left.pow (12 * n) 3
  have hsodd : Odd (r ^ 2 + r + 1) := by
    have h2odd : Odd (r ^ 2) := hr.pow (n := 2)
    have heven : Even (r ^ 2 + r) := Odd.add_odd h2odd hr
    exact Even.add_odd heven ⟨0, by norm_num⟩
  have hcop_s : Nat.Coprime (2 ^ (12 * n)) (r ^ 2 + r + 1) :=
    (hsodd.coprime_two_left).pow_left (12 * n)
  have hcop : Nat.Coprime (2 ^ (12 * n)) (r ^ 3 * (r ^ 2 + r + 1)) :=
    hcop_r.mul_right hcop_s
  rw [h2, h3] at h
  have hEq : r ^ 3 * ((r - 1) * (r + 1)) * ((r - 1) * (r ^ 2 + r + 1)) =
      ((r - 1) ^ 2 * (r + 1)) * (r ^ 3 * (r ^ 2 + r + 1)) := by ring
  exact hcop.dvd_of_dvd_mul_right (hEq ▸ h)

private theorem two_pow_twelve_dvd_su3_part {n r : ℕ} (hr : Odd r) (hr3 : 3 ≤ r)
    (h : 2 ^ (12 * n) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1)) :
    2 ^ (12 * n) ∣ (r - 1) * (r + 1) ^ 2 := by
  have hr1 : 1 ≤ r := by omega
  have h2 : r ^ 2 - 1 = (r - 1) * (r + 1) := pow_two_sub_one_eq r hr1
  have h3 : r ^ 3 + 1 = (r + 1) * (r ^ 2 - r + 1) := pow_three_add_one_eq r hr1
  have hcop_r : Nat.Coprime (2 ^ (12 * n)) (r ^ 3) :=
    hr.coprime_two_left.pow (12 * n) 3
  have hsodd : Odd (r ^ 2 - r + 1) := by
    have h2odd : Odd (r ^ 2) := hr.pow (n := 2)
    have heven : Even (r ^ 2 - r) := Nat.Odd.sub_odd h2odd hr
    exact Even.add_odd heven ⟨0, by norm_num⟩
  have hcop_s : Nat.Coprime (2 ^ (12 * n)) (r ^ 2 - r + 1) :=
    (hsodd.coprime_two_left).pow_left (12 * n)
  have hcop : Nat.Coprime (2 ^ (12 * n)) (r ^ 3 * (r ^ 2 - r + 1)) :=
    hcop_r.mul_right hcop_s
  rw [h2, h3] at h
  have hEq : r ^ 3 * ((r - 1) * (r + 1)) * ((r + 1) * (r ^ 2 - r + 1)) =
      ((r - 1) * (r + 1) ^ 2) * (r ^ 3 * (r ^ 2 - r + 1)) := by ring
  exact hcop.dvd_of_dvd_mul_right (hEq ▸ h)

private theorem ordTrialityD4_two_pow_lt {n : ℕ} (hn : 1 ≤ n) :
    ordTrialityD4 (2 ^ n) < 2 ^ (28 * n + 1) := by
  rw [ordTrialityD4_two_pow_eq]
  have hA : 2 ^ (8 * n) + 2 ^ (4 * n) + 1 < 2 * 2 ^ (8 * n) := by
    have hb : (2 ^ (4 * n)) ^ 2 = 2 ^ (8 * n) := by
      rw [← pow_mul]; congr 1; ring
    have hb2 : 2 ≤ 2 ^ (4 * n) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 1 ≤ 4 * n)
    nlinarith
  have hBpos : 0 < 2 ^ (6 * n) - 1 := by
    have h : 2 ≤ 2 ^ (6 * n) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 1 ≤ 6 * n)
    omega
  have hCpos : 0 < 2 ^ (2 * n) - 1 := by
    have h : 2 ≤ 2 ^ (2 * n) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 1 ≤ 2 * n)
    omega
  have hBC : (2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1) < 2 ^ (8 * n) := by
    have h1 : 2 ^ (6 * n) - 1 < 2 ^ (6 * n) := by omega
    have h2 : 2 ^ (2 * n) - 1 < 2 ^ (2 * n) := by omega
    calc (2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1) < 2 ^ (6 * n) * (2 ^ (2 * n) - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 hCpos
      _ < 2 ^ (6 * n) * 2 ^ (2 * n) :=
          Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 2 ^ (8 * n) := by rw [← pow_add]; congr 1; ring
  have h2 : (2:ℕ) * 2 ^ (8 * n) = 2 ^ (8 * n + 1) := (pow_succ' 2 (8 * n)).symm
  have hEq : 2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) * (2 ^ (6 * n) - 1) *
      (2 ^ (2 * n) - 1) =
      2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) *
        ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) := by ring
  rw [hEq]
  calc 2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) *
        ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1))
      < 2 ^ (12 * n) * (2 * 2 ^ (8 * n)) * ((2 ^ (6 * n) - 1) * (2 ^ (2 * n) - 1)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hA (by positivity))
          (mul_pos hBpos hCpos)
    _ < 2 ^ (12 * n) * (2 * 2 ^ (8 * n)) * 2 ^ (8 * n) :=
        Nat.mul_lt_mul_of_pos_left hBC (by positivity)
    _ = 2 ^ (28 * n + 1) := by
        rw [h2, ← pow_add, ← pow_add]
        congr 1
        ring

private theorem two_pow_four_lt_of_sl3 {n r : ℕ} (hr3 : 3 ≤ r)
    (hdiv : 2 ^ (12 * n) ∣ (r - 1) ^ 2 * (r + 1)) :
    2 ^ (4 * n) < r := by
  have hMpos : 0 < (r - 1) ^ 2 * (r + 1) := by
    have hr1 : 0 < r - 1 := by omega
    positivity
  have hMlt : (r - 1) ^ 2 * (r + 1) < r ^ 3 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hs : 2 ≤ s := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hklt : 2 ^ (12 * n) < r ^ 3 :=
    lt_of_le_of_lt (Nat.le_of_dvd hMpos hdiv) hMlt
  by_contra h
  push Not at h
  have h3 : r ^ 3 ≤ (2 ^ (4 * n)) ^ 3 := Nat.pow_le_pow_left h 3
  have hpow : (2 ^ (4 * n)) ^ 3 = 2 ^ (12 * n) := by rw [← pow_mul]; congr 1; ring
  omega

private theorem two_pow_four_le_sub_one_of_su3 {n r : ℕ} (hn : 1 ≤ n) (hr : Odd r) (hr3 : 3 ≤ r)
    (hdiv : 2 ^ (12 * n) ∣ (r - 1) * (r + 1) ^ 2) :
    2 ^ (4 * n) ≤ r - 1 := by
  have hMpos : 0 < (r - 1) * (r + 1) ^ 2 := by
    have hr1 : 0 < r - 1 := by omega
    positivity
  have hMlt : (r - 1) * (r + 1) ^ 2 < (r + 1) ^ 3 := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have hs : 2 ≤ s := by omega
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hklt : 2 ^ (12 * n) < (r + 1) ^ 3 :=
    lt_of_le_of_lt (Nat.le_of_dvd hMpos hdiv) hMlt
  have hlt : 2 ^ (4 * n) < r + 1 := by
    by_contra h
    push Not at h
    have h3 : (r + 1) ^ 3 ≤ (2 ^ (4 * n)) ^ 3 := Nat.pow_le_pow_left h 3
    have hpow : (2 ^ (4 * n)) ^ 3 = 2 ^ (12 * n) := by rw [← pow_mul]; congr 1; ring
    omega
  have hle : 2 ^ (4 * n) ≤ r := by omega
  have hne : 2 ^ (4 * n) ≠ r := by
    intro heq
    apply hr.not_two_dvd_nat
    rw [← heq]
    exact dvd_pow_self 2 (by omega : 4 * n ≠ 0)
  omega

private theorem pow_eight_le_sl3_rhs {r : ℕ} (hr3 : 3 ≤ r) :
    (r - 1) ^ 8 ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) := by
  have hr1 : 1 ≤ r := by omega
  have h1 : (r - 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (Nat.sub_le r 1) 3
  have h2 : (r - 1) ^ 2 ≤ r ^ 2 - 1 := by
    rw [pow_two_sub_one_eq r hr1]
    simpa [pow_two] using
      Nat.mul_le_mul_left (r - 1) (by omega : r - 1 ≤ r + 1)
  have h3 : (r - 1) ^ 3 ≤ r ^ 3 - 1 := by
    rw [pow_three_sub_one_eq r hr1]
    have hle : (r - 1) ^ 2 ≤ r ^ 2 + r + 1 :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le r 1) 2) (by omega)
    calc (r - 1) ^ 3 = (r - 1) * (r - 1) ^ 2 := by ring
      _ ≤ (r - 1) * (r ^ 2 + r + 1) := Nat.mul_le_mul_left (r - 1) hle
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hpow : (r - 1) ^ 3 * (r - 1) ^ 2 * (r - 1) ^ 3 = (r - 1) ^ 8 := by ring
  simpa [hpow] using h

private theorem pow_eight_le_su3_rhs {r : ℕ} (hr3 : 3 ≤ r) :
    (r - 1) ^ 8 ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
  have hr1 : 1 ≤ r := by omega
  have h1 : (r - 1) ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left (Nat.sub_le r 1) 3
  have h2 : (r - 1) ^ 2 ≤ r ^ 2 - 1 := by
    rw [pow_two_sub_one_eq r hr1]
    simpa [pow_two] using
      Nat.mul_le_mul_left (r - 1) (by omega : r - 1 ≤ r + 1)
  have h3 : (r - 1) ^ 3 ≤ r ^ 3 + 1 := by
    rw [pow_three_add_one_eq r hr1]
    have hle1 : r - 1 ≤ r + 1 := by omega
    have hle2 : (r - 1) ^ 2 ≤ r ^ 2 - r + 1 := by
      rw [pow_two_sub_self_eq r hr1]
      calc (r - 1) ^ 2 = (r - 1) * (r - 1) := by rw [pow_two]
        _ ≤ r * (r - 1) := Nat.mul_le_mul_right (r - 1) (by omega : r - 1 ≤ r)
        _ ≤ r * (r - 1) + 1 := Nat.le_add_right _ 1
    calc (r - 1) ^ 3 = (r - 1) * (r - 1) ^ 2 := by ring
      _ ≤ (r + 1) * (r ^ 2 - r + 1) := Nat.mul_le_mul hle1 hle2
  have h := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hpow : (r - 1) ^ 3 * (r - 1) ^ 2 * (r - 1) ^ 3 = (r - 1) ^ 8 := by ring
  simpa [hpow] using h

theorem ordTrialityD4_two_pow_mul_ne_sl3 {n r d : ℕ} (hn : 1 ≤ n) (hr : Odd r) (hr3 : 3 ≤ r)
    (hd : d ≤ 3) : ordTrialityD4 (2 ^ n) * d ≠ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) := by
  intro hEq
  have hNlt := ordTrialityD4_two_pow_lt hn
  have hNdlt : ordTrialityD4 (2 ^ n) * d < 2 ^ (28 * n + 3) := by
    have h1 : ordTrialityD4 (2 ^ n) * d ≤ ordTrialityD4 (2 ^ n) * 3 :=
      Nat.mul_le_mul_left _ hd
    have h2 : ordTrialityD4 (2 ^ n) * 3 < 2 ^ (28 * n + 1) * 3 :=
      Nat.mul_lt_mul_of_pos_right hNlt (by norm_num : 0 < 3)
    have h3 : 2 ^ (28 * n + 1) * 3 < 2 ^ (28 * n + 1) * 4 :=
      Nat.mul_lt_mul_of_pos_left (by norm_num : 3 < 4) (by positivity)
    have h4 : 2 ^ (28 * n + 1) * 4 = 2 ^ (28 * n + 3) := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    calc ordTrialityD4 (2 ^ n) * d ≤ ordTrialityD4 (2 ^ n) * 3 := h1
      _ < 2 ^ (28 * n + 1) * 3 := h2
      _ < 2 ^ (28 * n + 1) * 4 := h3
      _ = 2 ^ (28 * n + 3) := h4
  have hdivN : 2 ^ (12 * n) ∣ ordTrialityD4 (2 ^ n) :=
    two_pow_twelve_dvd_ordTrialityD4 n
  have hdivR : 2 ^ (12 * n) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) := by
    rw [← hEq]
    exact dvd_mul_of_dvd_left hdivN d
  have hdivM : 2 ^ (12 * n) ∣ (r - 1) ^ 2 * (r + 1) :=
    two_pow_twelve_dvd_sl3_part hr hr3 hdivR
  have hr4 : 2 ^ (4 * n) < r := two_pow_four_lt_of_sl3 hr3 hdivM
  have hRge : 2 ^ (28 * n + 4) ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) := by
    have h1 : (r - 1) ^ 8 ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) :=
      pow_eight_le_sl3_rhs hr3
    have h2 : (2 ^ (4 * n)) ^ 8 ≤ (r - 1) ^ 8 :=
      Nat.pow_le_pow_left (by omega : 2 ^ (4 * n) ≤ r - 1) 8
    have h3 : (2 ^ (4 * n)) ^ 8 = 2 ^ (32 * n) := by
      rw [← pow_mul]; congr 1; ring
    have h4 : 2 ^ (28 * n + 4) ≤ 2 ^ (32 * n) :=
      pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 28 * n + 4 ≤ 32 * n)
    calc 2 ^ (28 * n + 4) ≤ 2 ^ (32 * n) := h4
      _ = (2 ^ (4 * n)) ^ 8 := h3.symm
      _ ≤ (r - 1) ^ 8 := h2
      _ ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) := h1
  have hRlt : r ^ 3 * (r ^ 2 - 1) * (r ^ 3 - 1) < 2 ^ (28 * n + 3) := by
    rw [← hEq]
    exact hNdlt
  have hpowlt : 2 ^ (28 * n + 3) < 2 ^ (28 * n + 4) :=
    pow_lt_pow_right₀ (by norm_num : 1 < 2) (by omega)
  exact absurd hRge (not_le.mpr (lt_trans hRlt hpowlt))

theorem ordTrialityD4_two_pow_mul_ne_su3 {n r d : ℕ} (hn : 1 ≤ n) (hr : Odd r) (hr3 : 3 ≤ r)
    (hd : d ≤ 3) : ordTrialityD4 (2 ^ n) * d ≠ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
  intro hEq
  have hNlt := ordTrialityD4_two_pow_lt hn
  have hNdlt : ordTrialityD4 (2 ^ n) * d < 2 ^ (28 * n + 3) := by
    have h1 : ordTrialityD4 (2 ^ n) * d ≤ ordTrialityD4 (2 ^ n) * 3 :=
      Nat.mul_le_mul_left _ hd
    have h2 : ordTrialityD4 (2 ^ n) * 3 < 2 ^ (28 * n + 1) * 3 :=
      Nat.mul_lt_mul_of_pos_right hNlt (by norm_num : 0 < 3)
    have h3 : 2 ^ (28 * n + 1) * 3 < 2 ^ (28 * n + 1) * 4 :=
      Nat.mul_lt_mul_of_pos_left (by norm_num : 3 < 4) (by positivity)
    have h4 : 2 ^ (28 * n + 1) * 4 = 2 ^ (28 * n + 3) := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    calc ordTrialityD4 (2 ^ n) * d ≤ ordTrialityD4 (2 ^ n) * 3 := h1
      _ < 2 ^ (28 * n + 1) * 3 := h2
      _ < 2 ^ (28 * n + 1) * 4 := h3
      _ = 2 ^ (28 * n + 3) := h4
  have hdivN : 2 ^ (12 * n) ∣ ordTrialityD4 (2 ^ n) :=
    two_pow_twelve_dvd_ordTrialityD4 n
  have hdivR : 2 ^ (12 * n) ∣ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
    rw [← hEq]
    exact dvd_mul_of_dvd_left hdivN d
  have hdivM : 2 ^ (12 * n) ∣ (r - 1) * (r + 1) ^ 2 :=
    two_pow_twelve_dvd_su3_part hr hr3 hdivR
  have hr4 : 2 ^ (4 * n) ≤ r - 1 := two_pow_four_le_sub_one_of_su3 hn hr hr3 hdivM
  have hRge : 2 ^ (28 * n + 4) ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := by
    have h1 : (r - 1) ^ 8 ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) :=
      pow_eight_le_su3_rhs hr3
    have h2 : (2 ^ (4 * n)) ^ 8 ≤ (r - 1) ^ 8 :=
      Nat.pow_le_pow_left hr4 8
    have h3 : (2 ^ (4 * n)) ^ 8 = 2 ^ (32 * n) := by
      rw [← pow_mul]; congr 1; ring
    have h4 : 2 ^ (28 * n + 4) ≤ 2 ^ (32 * n) :=
      pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 2) (by omega : 28 * n + 4 ≤ 32 * n)
    calc 2 ^ (28 * n + 4) ≤ 2 ^ (32 * n) := h4
      _ = (2 ^ (4 * n)) ^ 8 := h3.symm
      _ ≤ (r - 1) ^ 8 := h2
      _ ≤ r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) := h1
  have hRlt : r ^ 3 * (r ^ 2 - 1) * (r ^ 3 + 1) < 2 ^ (28 * n + 3) := by
    rw [← hEq]
    exact hNdlt
  have hpowlt : 2 ^ (28 * n + 3) < 2 ^ (28 * n + 4) :=
    pow_lt_pow_right₀ (by norm_num : 1 < 2) (by omega)
  exact absurd hRge (not_le.mpr (lt_trans hRlt hpowlt))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core
