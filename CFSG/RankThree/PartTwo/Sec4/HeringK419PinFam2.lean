module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinFam

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.RankThree.PartTwo.KFacts.OddChar
open CFSG.RankThree.PartTwo.Sec11.KSListsProof

theorem two_pow_padicValNat_u4_le {q : ℕ} (hq : Odd q) (hq1 : 1 < q) :
    2 ^ padicValNat 2 ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) ≤ 8 * (q + 1) ^ 3 := by
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h4 := pow_sub_one_ne_zero hq1 (j := 4) (by norm_num)
  have h3 : q ^ 3 + 1 ≠ 0 := by omega
  rw [padicValNat.mul (Nat.mul_ne_zero h2 h3) h4, padicValNat.mul h2 h3,
    padicValNat_pow_three_add_one hq, padicValNat_pow_four_sub_one hq hq1]
  have e1 := two_pow_padicValNat_sq_sub_one_le hq hq1
  have e2 := two_pow_padicValNat_le (n := q + 1) (by omega)
  calc 2 ^ (padicValNat 2 (q ^ 2 - 1) + padicValNat 2 (q + 1) +
        (padicValNat 2 (q ^ 2 - 1) + 1))
      = 2 * (2 ^ padicValNat 2 (q ^ 2 - 1) * 2 ^ padicValNat 2 (q + 1) *
          2 ^ padicValNat 2 (q ^ 2 - 1)) := by ring
    _ ≤ 2 * ((2 * (q + 1)) * (q + 1) * (2 * (q + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e1)
    _ = 8 * (q + 1) ^ 3 := by ring

theorem u4_two_ineq8 {Q : ℕ} (hQ : 5 ≤ Q) :
    (8 * (Q + 1) ^ 3) ^ 8 * 4 ^ 3 ≤ (Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1))) ^ 3 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 5 := ⟨Q - 5, by omega⟩
  have h1 : 1 ≤ (t + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (t + 5) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h3]
  have : (0 : ℤ) ≤ (((t : ℤ) + 5) ^ 6 * ((((t : ℤ) + 5) ^ 2 - 1) * (((t : ℤ) + 5) ^ 3 + 1) *
      (((t : ℤ) + 5) ^ 4 - 1))) ^ 3 - (8 * ((t : ℤ) + 5 + 1) ^ 3) ^ 8 * 4 ^ 3 := by
    ring_nf
    positivity
  linarith

theorem two_pow_le_of_mul_eq_u4 {q N g : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hN : N * g = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))) (hg : g ∣ 4) :
    2 ^ (8 * padicValNat 2 N) ≤ N ^ 3 := by
  have hq1 : 1 < q := by omega
  have h2 := pow_sub_one_ne_zero hq1 (j := 2) (by norm_num)
  have h4 := pow_sub_one_ne_zero hq1 (j := 4) (by norm_num)
  have h3 : q ^ 3 + 1 ≠ 0 := by omega
  have hC0 : (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero h2 h3) h4
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hg4 : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hN
    exact Nat.mul_ne_zero (pow_ne_zero 6 (by omega)) hC0 hN.symm
  have hv : padicValNat 2 N ≤ padicValNat 2 ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
    have h := congrArg (padicValNat 2) hN
    rw [padicValNat.mul hN0 hg0, padicValNat_odd_pow_mul hq _ hC0] at h
    omega
  have hb : 2 ^ padicValNat 2 N ≤ 8 * (q + 1) ^ 3 :=
    (Nat.pow_le_pow_right (by norm_num) hv).trans (two_pow_padicValNat_u4_le hq hq1)
  have : 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ N ^ 3 * g ^ 3 :=
    calc 2 ^ (8 * padicValNat 2 N) * g ^ 3 ≤ (8 * (q + 1) ^ 3) ^ 8 * 4 ^ 3 := by
          rw [pow_mul']
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hb 8) (Nat.pow_le_pow_left hg4 3)
      _ ≤ (q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))) ^ 3 := u4_two_ineq8 hq5
      _ = N ^ 3 * g ^ 3 := by rw [← hN, mul_pow]
  exact Nat.le_of_mul_le_mul_right this (pow_pos (Nat.pos_of_ne_zero hg0) 3)

theorem sl3_ineq {Q : ℕ} (hQ : 46 ≤ Q) :
    (3 * (Q + 1) ^ 2) ^ 5 * 3 ^ 2 ≤ (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 46 := ⟨Q - 46, by omega⟩
  have h1 : 1 ≤ (t + 46) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 46) ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤
      (((t : ℤ) + 46) ^ 3 * ((((t : ℤ) + 46) ^ 2 - 1) * (((t : ℤ) + 46) ^ 3 - 1))) ^ 2 -
      (3 * ((t : ℤ) + 46 + 1) ^ 2) ^ 5 * 3 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem su3_ineq {Q : ℕ} (hQ : 46 ≤ Q) :
    (3 * (Q + 1) ^ 2) ^ 5 * 3 ^ 2 ≤ (Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 46 := ⟨Q - 46, by omega⟩
  have h1 : 1 ≤ (t + 46) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) ≤
      (((t : ℤ) + 46) ^ 3 * ((((t : ℤ) + 46) ^ 2 - 1) * (((t : ℤ) + 46) ^ 3 + 1))) ^ 2 -
      (3 * ((t : ℤ) + 46 + 1) ^ 2) ^ 5 * 3 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem sp4_ineq {Q : ℕ} (hQ : 46 ≤ Q) :
    (3 * (Q + 1) ^ 2) ^ 5 * 2 ^ 2 ≤ (Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 46 := ⟨Q - 46, by omega⟩
  have h1 : 1 ≤ (t + 46) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 46) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤
      (((t : ℤ) + 46) ^ 4 * ((((t : ℤ) + 46) ^ 2 - 1) * (((t : ℤ) + 46) ^ 4 - 1))) ^ 2 -
      (3 * ((t : ℤ) + 46 + 1) ^ 2) ^ 5 * 2 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem l4_ineq {Q : ℕ} (hQ : 12 ≤ Q) :
    (3 * (Q + 1) ^ 3) ^ 5 * 4 ^ 2 ≤ (Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 - 1) * (Q ^ 4 - 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 12 := ⟨Q - 12, by omega⟩
  have h1 : 1 ≤ (t + 12) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 12) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (t + 12) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3]
  have : (0 : ℤ) ≤ (((t : ℤ) + 12) ^ 6 * ((((t : ℤ) + 12) ^ 2 - 1) * (((t : ℤ) + 12) ^ 3 - 1) *
      (((t : ℤ) + 12) ^ 4 - 1))) ^ 2 - (3 * ((t : ℤ) + 12 + 1) ^ 3) ^ 5 * 4 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem u4_ineq {Q : ℕ} (hQ : 12 ≤ Q) :
    (3 * (Q + 1) ^ 3) ^ 5 * 4 ^ 2 ≤ (Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 12 := ⟨Q - 12, by omega⟩
  have h1 : 1 ≤ (t + 12) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (t + 12) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h3]
  have : (0 : ℤ) ≤ (((t : ℤ) + 12) ^ 6 * ((((t : ℤ) + 12) ^ 2 - 1) * (((t : ℤ) + 12) ^ 3 + 1) *
      (((t : ℤ) + 12) ^ 4 - 1))) ^ 2 - (3 * ((t : ℤ) + 12 + 1) ^ 3) ^ 5 * 4 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem g2_ineq {Q : ℕ} (hQ : 46 ≤ Q) :
    (3 * (Q + 1) ^ 2) ^ 5 * 1 ^ 2 ≤ (Q ^ 6 * ((Q ^ 6 - 1) * (Q ^ 2 - 1))) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, Q = t + 46 := ⟨Q - 46, by omega⟩
  have h1 : 1 ≤ (t + 46) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (t + 46) ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2]
  have : (0 : ℤ) ≤
      (((t : ℤ) + 46) ^ 6 * ((((t : ℤ) + 46) ^ 6 - 1) * (((t : ℤ) + 46) ^ 2 - 1))) ^ 2 -
      (3 * ((t : ℤ) + 46 + 1) ^ 2) ^ 5 * 1 ^ 2 := by
    ring_nf
    positivity
  linarith

theorem not_two_dvd_pow_add_one {f a : ℕ} (hf : 0 < f) (ha : 0 < a) : ¬ 2 ∣ (2 ^ f) ^ a + 1 :=
  fun h => (Nat.not_even_iff_odd.mpr (odd_pow_add_one hf ha)) (even_iff_two_dvd.mpr h)

theorem not_two_dvd_pow_sub_one' {f a : ℕ} (hf : 0 < f) (ha : 0 < a) : ¬ 2 ∣ (2 ^ f) ^ a - 1 :=
  fun h => (Nat.not_even_iff_odd.mpr (odd_pow_sub_one hf ha)) (even_iff_two_dvd.mpr h)

theorem not_two_dvd_two_pow_sub_one {f : ℕ} (hf : 0 < f) : ¬ 2 ∣ 2 ^ f - 1 :=
  fun h => (Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one hf)) (even_iff_two_dvd.mpr h)

theorem eq_three_of_dvd_three {s d : ℕ} (hs : s.Prime) (hd : d ∣ 3) (h : s ∣ d) : s = 3 :=
  (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (h.trans hd)

theorem ge_46_of {Q : ℕ} (h : 3 ^ 8 ≤ 3 * (Q + 1) ^ 2) : 46 ≤ Q := by
  by_contra hlt
  push Not at hlt
  have : Q + 1 ≤ 46 := by omega
  have h2 : (Q + 1) ^ 2 ≤ 46 ^ 2 := Nat.pow_le_pow_left this 2
  omega

theorem ge_12_of {Q : ℕ} (h : 3 ^ 8 ≤ 3 * (Q + 1) ^ 3) : 12 ≤ Q := by
  by_contra hlt
  push Not at hlt
  have : Q + 1 ≤ 12 := by omega
  have h2 : (Q + 1) ^ 3 ≤ 12 ^ 3 := Nat.pow_le_pow_left this 3
  omega

theorem not_sl3 {M p e s g d : ℕ} (hX : XInfo M p e) (hs : s.Prime) (hg : 1 ≤ g)
    (hcond : s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) (hd3 : d ∣ 3)
    (hform : (d ∣ s ^ g - 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1))) ∨
      (d ∣ s ^ g + 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1)))) :
    False := by
  have hQ2 : 2 ≤ s ^ g := le_trans hs.two_le (Nat.le_self_pow (by omega) s)
  have hsQ : s ∣ s ^ g := dvd_pow_self s (by omega)
  have hdle : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd3
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd3 (by norm_num)
  have hds : ¬ s ∣ d := fun h => by
    have := eq_three_of_dvd_three hs hd3 h
    rcases hcond with h2 | ⟨h5, -⟩ <;> omega
  have hN : s ≠ 2 → g * 3 < 8 := fun hs2 => by
    rcases hcond with h | ⟨-, hg2⟩
    · exact absurd h hs2
    · omega
  have hodd : s ≠ 2 → Odd (s ^ g) := fun hs2 => (hs.odd_of_ne_two hs2).pow
  have h5 : s ≠ 2 → 5 ≤ s ^ g := fun hs2 => by
    rcases hcond with h | ⟨h5, -⟩
    · exact absurd h hs2
    · exact h5.trans (Nat.le_self_pow (by omega) s)
  have hK6 : p = 2 → 6 ≤ padicValNat 2 M := fun hp2 => by
    obtain ⟨k, hk8, hdvd, hndvd, -⟩ := hX.ex
    subst hp2
    have hv := padicValNat_eq_of_exact hX.prime hdvd hndvd
    omega
  rcases hform with ⟨hdq, h⟩ | ⟨hdq, h⟩
  · refine family_core (C := ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1)) (N := 3) (dmax := 3)
      (B := 3 * (s ^ g + 1) ^ 2) hX hs hg h hdle (by norm_num) ?_ hds hN ?_ ?_ ?_ ?_ ?_
    · intro hh
      rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
      · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
      · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
    · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_sl3 hr hr2 hQ2 hrk
    · exact fun _ hB => sl3_ineq (ge_46_of hB)
    · intro hs2 hp2
      refine two_pow_le_of_mul_eq_slOrd (hodd hs2) (by have := h5 hs2; omega)
        (by norm_num : 3 ≤ 3) ?_ hdq
      rw [h, show 3 * (3 - 1) / 2 = 3 from rfl, show Icc 2 3 = {2, 3} by rfl,
        prod_pair (by norm_num)]
    · intro hs2
      subst hs2
      exact cube_lt_of_lt_pow (D := 8) hd1 (by rw [h]; exact sl3a_lt hQ2) hQ2 (by norm_num)
    · intro hs2
      subst hs2
      refine ⟨3 * g, by omega, by omega, fun q hq => ⟨?_, fun hqd => ?_⟩⟩
      · have h1 := (PrimDiv.dvd_pow_sub_one_iff hq (by omega) g 3).mpr ⟨1, by ring⟩
        exact Dvd.dvd.mul_left h1 _
      · have := hq.eq_two_of_dvd_three (by omega) (hqd.trans hd3)
        omega
  · refine family_core (C := ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1)) (N := 3) (dmax := 3)
      (B := 3 * (s ^ g + 1) ^ 2) hX hs hg h hdle (by norm_num) ?_ hds hN ?_ ?_ ?_ ?_ ?_
    · intro hh
      rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
      · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
      · exact not_dvd_pow_add_one hs hsQ (by norm_num) h1
    · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_su3 hr hr2 hQ2 hrk
    · exact fun _ hB => su3_ineq (ge_46_of hB)
    · intro hs2 hp2
      refine two_pow_le_of_mul_eq_su3 (hodd hs2) (by omega) ?_ hd3 (hK6 hp2)
      rw [h, mul_assoc]
    · intro hs2
      subst hs2
      exact cube_lt_of_lt_pow (D := 8) hd1 (by rw [h]; exact sl3b_lt hQ2) hQ2 (by norm_num)
    · intro hs2
      subst hs2
      refine ⟨6 * g, by omega, by omega, fun q hq => ⟨?_, fun hqd => ?_⟩⟩
      · have h1 := (PrimDiv.dvd_pow_add_one_iff hq (by omega) g 3).mpr
          ⟨⟨1, by ring⟩, fun hh => by
            have := Nat.le_of_dvd (by omega) hh
            omega⟩
        exact Dvd.dvd.mul_left h1 _
      · have := hq.eq_two_of_dvd_three (by omega) (hqd.trans hd3)
        omega

theorem not_sp4 {M p e s g d : ℕ} (hX : XInfo M p e) (hs : s.Prime) (hg : 1 ≤ g)
    (hcond : s = 2 ∨ (5 ≤ s ∧ g = 1))
    (hd : (Even (s ^ g) ∧ d = 1) ∨ (Odd (s ^ g) ∧ d = 2))
    (h : M * d = (s ^ g) ^ 4 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 4 - 1))) : False := by
  have hQ2 : 2 ≤ s ^ g := le_trans hs.two_le (Nat.le_self_pow (by omega) s)
  have hsQ : s ∣ s ^ g := dvd_pow_self s (by omega)
  have hd2 : d ≤ 2 := by rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hd1 : 1 ≤ d := by rcases hd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  have hd_two : s = 2 → d = 1 := fun hs2 => by
    subst hs2
    rcases hd with ⟨-, h1⟩ | ⟨ho, -⟩
    · exact h1
    · exact absurd (Nat.even_pow.mpr ⟨even_two, by omega⟩) (Nat.not_even_iff_odd.mpr ho)
  have hds : ¬ s ∣ d := fun hh => by
    rcases hcond with h2 | ⟨h5, -⟩
    · rw [hd_two h2] at hh
      exact hs.one_lt.ne' (Nat.dvd_one.mp hh)
    · have : d ≤ 2 := hd2
      have := Nat.le_of_dvd (by omega) hh
      omega
  have hN : s ≠ 2 → g * 4 < 8 := fun hs2 => by
    rcases hcond with h | ⟨-, hg2⟩
    · exact absurd h hs2
    · omega
  refine family_core (C := ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 4 - 1)) (N := 4) (dmax := 2)
    (B := 3 * (s ^ g + 1) ^ 2) hX hs hg h hd2 (by norm_num) ?_ hds hN ?_ ?_ ?_ ?_ ?_
  · intro hh
    rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
    · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
    · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
  · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_sp4 hr hr2 hQ2 hrk
  · exact fun _ hB => sp4_ineq (ge_46_of hB)
  · intro hs2 hp2
    have hodd : Odd (s ^ g) := (hs.odd_of_ne_two hs2).pow
    have h5 : 5 ≤ s ^ g := by
      rcases hcond with h | ⟨h5, -⟩
      · exact absurd h hs2
      · exact h5.trans (Nat.le_self_pow (by omega) s)
    have hd2' : d = 2 := by
      rcases hd with ⟨he, -⟩ | ⟨-, h2⟩
      · exact absurd he (Nat.not_even_iff_odd.mpr hodd)
      · exact h2
    subst hd2'
    refine two_pow_le_of_mul_two_eq_spOrd hodd (by omega) (Or.inr ⟨rfl, h5⟩) ?_
    rw [h, show 2 ^ 2 = 4 by norm_num, show Icc 1 2 = {1, 2} by rfl, prod_pair (by norm_num)]
  · intro hs2
    subst hs2
    exact cube_lt_of_lt_pow (D := 10) hd1 (by rw [h]; exact sp4_lt hQ2) hQ2 (by norm_num)
  · intro hs2
    subst hs2
    refine ⟨4 * g, by omega, by omega, fun q hq => ⟨?_, fun hqd => ?_⟩⟩
    · have h1 := (PrimDiv.dvd_pow_sub_one_iff hq (by omega) g 4).mpr ⟨1, by ring⟩
      exact Dvd.dvd.mul_left h1 _
    · rw [hd_two rfl] at hqd
      exact hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)

theorem not_u4 {M p e s g d : ℕ} (hX : XInfo M p e) (hs : s.Prime) (hg : 1 ≤ g)
    (hcond : s = 2 ∨ (5 ≤ s ∧ g = 1)) (hd4 : d ∣ 4) (hdq : d ∣ s ^ g + 1)
    (h : M * d = (s ^ g) ^ 6 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) * ((s ^ g) ^ 4 - 1))) :
    False := by
  have hQ2 : 2 ≤ s ^ g := le_trans hs.two_le (Nat.le_self_pow (by omega) s)
  have hsQ : s ∣ s ^ g := dvd_pow_self s (by omega)
  have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
  have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd4 (by norm_num)
  have hd_two : s = 2 → d = 1 := fun hs2 => by
    subst hs2
    have hodd : Odd (2 ^ g + 1) :=
      (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    have hdodd : Odd d := hodd.of_dvd_nat hdq
    have : d ∣ 4 := hd4
    have hd' : d = 1 ∨ d = 2 ∨ d = 4 := by
      have : d ≤ 4 := hdle
      interval_cases d <;> simp_all <;> omega
    rcases hd' with h1 | h2 | h4
    · exact h1
    · exact absurd hdodd (by rw [h2]; decide)
    · exact absurd hdodd (by rw [h4]; decide)
  have hds : ¬ s ∣ d := fun hh => by
    rcases hcond with h2 | ⟨h5, -⟩
    · rw [hd_two h2] at hh
      exact hs.one_lt.ne' (Nat.dvd_one.mp hh)
    · have := Nat.le_of_dvd (by omega) hh
      omega
  have hN : s ≠ 2 → g * 6 < 8 := fun hs2 => by
    rcases hcond with h | ⟨-, hg2⟩
    · exact absurd h hs2
    · omega
  have hodd : s ≠ 2 → Odd (s ^ g) := fun hs2 => (hs.odd_of_ne_two hs2).pow
  have h5 : s ≠ 2 → 5 ≤ s ^ g := fun hs2 => by
    rcases hcond with h | ⟨h5, -⟩
    · exact absurd h hs2
    · exact h5.trans (Nat.le_self_pow (by omega) s)
  refine family_core (C := ((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) * ((s ^ g) ^ 4 - 1))
    (N := 6) (dmax := 4) (B := 3 * (s ^ g + 1) ^ 3) hX hs hg h hdle (by norm_num) ?_ hds hN
    ?_ ?_ ?_ ?_ ?_
  · intro hh
    rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
    · rcases (Nat.Prime.dvd_mul hs).mp h1 with h1 | h1
      · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
      · exact not_dvd_pow_add_one hs hsQ (by norm_num) h1
    · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
  · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_u4 hr hr2 hQ2 hrk
  · exact fun _ hB => u4_ineq (ge_12_of hB)
  · intro hs2 hp2
    exact two_pow_le_of_mul_eq_u4 (hodd hs2) (h5 hs2) h hd4
  · intro hs2
    subst hs2
    exact cube_lt_of_lt_pow (D := 15) hd1 (by rw [h]; exact u4_lt hQ2) hQ2 (by norm_num)
  · intro hs2
    subst hs2
    refine ⟨6 * g, by omega, by omega, fun q hq => ⟨?_, fun hqd => ?_⟩⟩
    · have h1 := (PrimDiv.dvd_pow_add_one_iff hq (by omega) g 3).mpr
        ⟨⟨1, by ring⟩, fun hh => by
          have := Nat.le_of_dvd (by omega) hh
          omega⟩
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
    · rw [hd_two rfl] at hqd
      exact hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)

theorem not_l4 {M p e s d : ℕ} (hX : XInfo M p e) (hs : s.Prime) (h5 : 5 ≤ s) (hd4 : d ∣ 4)
    (hdq : d ∣ s - 1) (h : M * d = s ^ 6 * ((s ^ 2 - 1) * (s ^ 3 - 1) * (s ^ 4 - 1))) : False := by
  have hs2 : s ≠ 2 := by omega
  have hdle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
  have hds : ¬ s ∣ d := fun hh => by
    have := Nat.le_of_dvd (by omega) (hh.trans hd4)
    omega
  have hodd : Odd s := hs.odd_of_ne_two hs2
  have hMC : M * d = (s ^ 1) ^ 6 * ((s ^ 2 - 1) * (s ^ 3 - 1) * (s ^ 4 - 1)) := by
    rw [pow_one]; exact h
  refine family_core (C := (s ^ 2 - 1) * (s ^ 3 - 1) * (s ^ 4 - 1)) (g := 1) (N := 6)
    (dmax := 4) (B := 3 * (s + 1) ^ 3) hX hs le_rfl hMC hdle (by norm_num) ?_ hds
    (fun _ => by norm_num) ?_ ?_ ?_ (fun h => absurd h hs2) (fun h => absurd h hs2)
  · intro hh
    rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
    · rcases (Nat.Prime.dvd_mul hs).mp h1 with h1 | h1
      · exact not_dvd_pow_sub_one hs (dvd_refl s) (by omega) (by norm_num) h1
      · exact not_dvd_pow_sub_one hs (dvd_refl s) (by omega) (by norm_num) h1
    · exact not_dvd_pow_sub_one hs (dvd_refl s) (by omega) (by norm_num) h1
  · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_l4 hr hr2 (by omega) hrk
  · intro _ hB
    have := l4_ineq (ge_12_of (by simpa [pow_one] using hB))
    simpa [pow_one] using this
  · intro _ hp2
    refine two_pow_le_of_mul_eq_slOrd hodd (by omega) (by norm_num : 3 ≤ 4) ?_ hdq
    rw [h, show 4 * (4 - 1) / 2 = 6 from rfl, show Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide,
      prod_insert (by decide), prod_pair (by norm_num), mul_assoc]

theorem not_g2 {M p e s g : ℕ} (hX : XInfo M p e) (hs : s.Prime) (hg : 1 ≤ g)
    (hcond : s = 2 ∨ (5 ≤ s ∧ g = 1)) (h : M = ordG2 (s ^ g)) : False := by
  have hQ2 : 2 ≤ s ^ g := le_trans hs.two_le (Nat.le_self_pow (by omega) s)
  have hsQ : s ∣ s ^ g := dvd_pow_self s (by omega)
  have hds : ¬ s ∣ 1 := fun hh => hs.one_lt.ne' (Nat.dvd_one.mp hh)
  have hMC : M * 1 = (s ^ g) ^ 6 * (((s ^ g) ^ 6 - 1) * ((s ^ g) ^ 2 - 1)) := by
    rw [h, mul_one, ordG2, mul_assoc]
  have hN : s ≠ 2 → g * 6 < 8 := fun hs2 => by
    rcases hcond with h | ⟨-, hg2⟩
    · exact absurd h hs2
    · omega
  have hodd : s ≠ 2 → Odd (s ^ g) := fun hs2 => (hs.odd_of_ne_two hs2).pow
  have h5 : s ≠ 2 → 5 ≤ s ^ g := fun hs2 => by
    rcases hcond with h | ⟨h5, -⟩
    · exact absurd h hs2
    · exact h5.trans (Nat.le_self_pow (by omega) s)
  refine family_core (C := ((s ^ g) ^ 6 - 1) * ((s ^ g) ^ 2 - 1)) (N := 6) (d := 1) (dmax := 1)
    (B := 3 * (s ^ g + 1) ^ 2) hX hs hg hMC le_rfl (by norm_num) ?_ hds hN ?_ ?_ ?_ ?_ ?_
  · intro hh
    rcases (Nat.Prime.dvd_mul hs).mp hh with h1 | h1
    · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
    · exact not_dvd_pow_sub_one hs hsQ (by omega) (by norm_num) h1
  · exact fun _ r k hr hr2 hrk => pow_le_of_dvd_g2 hr hr2 hQ2 hrk
  · exact fun _ hB => g2_ineq (ge_46_of hB)
  · intro hs2 hp2
    have := two_pow_le_g2 (hodd hs2) (by have := h5 hs2; omega)
    rw [h, ordG2]
    exact this
  · intro hs2
    subst hs2
    exact cube_lt_of_lt_pow (d := 1) (D := 14) le_rfl (by rw [mul_one, h]; exact ordG2_lt_pow hQ2)
      hQ2 (by norm_num)
  · intro hs2
    subst hs2
    refine ⟨6 * g, by omega, by omega, fun q hq => ⟨?_, fun hqd => ?_⟩⟩
    · have h1 := (PrimDiv.dvd_pow_sub_one_iff hq (by omega) g 6).mpr ⟨1, by ring⟩
      exact Dvd.dvd.mul_right h1 _
    · exact hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)

theorem not_d4 {M p e f : ℕ} (hX : XInfo M p e) (hf : 1 ≤ f) (h : M = ordTrialityD4 (2 ^ f)) :
    False := by
  have hQ2 : 2 ≤ 2 ^ f := le_trans Nat.prime_two.two_le (Nat.le_self_pow (by omega) 2)
  have hMC : M * 1 = (2 ^ f) ^ 12 *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    rw [h, mul_one, ordTrialityD4]; ring
  have hds : ¬ 2 ∣ 1 := by norm_num
  have hCs : ¬ 2 ∣ (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    intro hh
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hh with h1 | h1
    · have he : Even ((2 ^ f) ^ 8 + (2 ^ f) ^ 4) := by
        rw [← pow_mul, ← pow_mul]
        exact ((Nat.even_pow' (by omega)).mpr even_two).add
          ((Nat.even_pow' (by omega)).mpr even_two)
      exact (Nat.not_even_iff_odd.mpr he.add_one) (even_iff_two_dvd.mpr h1)
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h1 | h1
      · exact not_two_dvd_pow_sub_one' (by omega) (by norm_num) h1
      · exact not_two_dvd_pow_sub_one' (by omega) (by norm_num) h1
  refine family_core (s := 2) (g := f)
    (C := ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)))
    (N := 12) (d := 1) (dmax := 1) (B := 0) hX Nat.prime_two hf hMC le_rfl (by norm_num) hCs hds
    (fun h => absurd rfl h) (fun h => absurd rfl h) (fun h => absurd rfl h)
    (fun h => absurd rfl h) ?_ ?_
  · intro _
    exact cube_lt_of_lt_pow (d := 1) (D := 28) le_rfl
      (by rw [mul_one, h]; exact ordTrialityD4_lt_pow hQ2) hQ2 (by norm_num)
  · intro _
    refine ⟨12 * f, by omega, by omega, fun q hq => ⟨?_, fun hqd =>
      hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)⟩⟩
    have h1 := PrimDiv.dvd_triality_of hq (by omega) f ⟨1, by ring⟩ (fun hh => by
      have := Nat.le_of_dvd (by omega) hh
      omega)
    exact Dvd.dvd.mul_right h1 _

theorem not_sz {M p e f : ℕ} (hX : XInfo M p e) (hf : 1 ≤ f) (h : M = ordSuzuki (2 ^ f)) :
    False := by
  have hQ2 : 2 ≤ 2 ^ f := le_trans Nat.prime_two.two_le (Nat.le_self_pow (by omega) 2)
  have hMC : M * 1 = (2 ^ f) ^ 2 * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    rw [h, mul_one, ordSuzuki, mul_assoc]
  have hds : ¬ 2 ∣ 1 := by norm_num
  have hCs : ¬ 2 ∣ (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    intro hh
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hh with h1 | h1
    · exact not_two_dvd_pow_add_one (by omega) (by norm_num) h1
    · exact not_two_dvd_two_pow_sub_one (by omega) h1
  refine family_core (s := 2) (g := f) (C := ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) (N := 2) (d := 1)
    (dmax := 1) (B := 0) hX Nat.prime_two hf hMC le_rfl (by norm_num) hCs hds
    (fun h => absurd rfl h) (fun h => absurd rfl h) (fun h => absurd rfl h)
    (fun h => absurd rfl h) ?_ ?_
  · intro _
    exact cube_lt_of_lt_pow (d := 1) (D := 5) le_rfl
      (by rw [mul_one, h, ordSuzuki, mul_assoc]; exact sz_lt hQ2) hQ2 (by norm_num)
  · intro _
    refine ⟨4 * f, by omega, by omega, fun q hq => ⟨?_, fun hqd =>
      hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)⟩⟩
    have h1 := (PrimDiv.dvd_pow_add_one_iff hq (by omega) f 2).mpr
      ⟨⟨1, by ring⟩, fun hh => by
        have := Nat.le_of_dvd (by omega) hh
        omega⟩
    exact Dvd.dvd.mul_right h1 _

theorem not_f4t {M p e f : ℕ} (hX : XInfo M p e) (hf : 1 ≤ f)
    (h : M = ordTwistedF4 (2 ^ f)) : False := by
  have hQ2 : 2 ≤ 2 ^ f := le_trans Nat.prime_two.two_le (Nat.le_self_pow (by omega) 2)
  have hMC : M * 1 = (2 ^ f) ^ 12 * (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    rw [h, mul_one, ordTwistedF4]; ring
  have hds : ¬ 2 ∣ 1 := by norm_num
  have hCs : ¬ 2 ∣ (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    intro hh
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hh with h1 | h1
    · exact not_two_dvd_pow_add_one (by omega) (by norm_num) h1
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h1 | h1
      · exact not_two_dvd_pow_sub_one' (by omega) (by norm_num) h1
      · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h1 with h1 | h1
        · exact not_two_dvd_pow_add_one (by omega) (by norm_num) h1
        · exact not_two_dvd_two_pow_sub_one (by omega) h1
  refine family_core (s := 2) (g := f) (C := ((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) (N := 12) (d := 1) (dmax := 1) (B := 0) hX
    Nat.prime_two hf hMC le_rfl (by norm_num) hCs hds (fun h => absurd rfl h)
    (fun h => absurd rfl h) (fun h => absurd rfl h) (fun h => absurd rfl h) ?_ ?_
  · intro _
    exact cube_lt_of_lt_pow (d := 1) (D := 26) le_rfl (by rw [mul_one, h]; exact f4t_lt hQ2) hQ2
      (by norm_num)
  · intro _
    refine ⟨12 * f, by omega, by omega, fun q hq => ⟨?_, fun hqd =>
      hq.prime.one_lt.ne' (Nat.dvd_one.mp hqd)⟩⟩
    have h1 := (PrimDiv.dvd_pow_add_one_iff hq (by omega) f 6).mpr
      ⟨⟨1, by ring⟩, fun hh => by
        have := Nat.le_of_dvd (by omega) hh
        omega⟩
    exact Dvd.dvd.mul_right h1 _

end CFSG.RankThree.PartTwo.Sec4.HeringPin
