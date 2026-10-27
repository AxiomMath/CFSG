module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

open CFSG.LocalAnalysis.WeakClosure81 (dihedralDeg)

@[expose] def orbLen (p e : ℕ) : ℕ :=
  if Even e then (p ^ e - 1) / (2 * (p - 1)) else (p ^ e - 1) / (p - 1)

private theorem dParam_eq_of_forall {p n : ℕ} (hn : 0 < n) (h1 : (2 : ZMod p) ^ n = 1)
    (h2 : ∀ m < n, 0 < m → (2 : ZMod p) ^ m ≠ 1) : dParam p = n := by
  rw [dParam]
  exact (orderOf_eq_iff hn).2 ⟨h1, h2⟩

private theorem dvd_two_pow_dParam_sub_one (p : ℕ) : p ∣ 2 ^ dParam p - 1 := by
  have h1 : 1 ≤ 2 ^ dParam p := Nat.one_le_two_pow
  have h : ((2 ^ dParam p - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_ofNat, pow_dParam p]
    norm_num
  exact (ZMod.natCast_eq_zero_iff (2 ^ dParam p - 1) p).1 h

theorem dParam_eq_of_small : dParam 3 = 2 ∧ dParam 5 = 4 ∧ dParam 7 = 3 ∧ dParam 17 = 8 ∧
    dParam 31 = 5 ∧ dParam 73 = 9 ∧ dParam 127 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m; decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)
  · exact dParam_eq_of_forall (by norm_num) (by decide)
      (by intro m hm _; interval_cases m <;> decide)

private theorem not_dParam_four_six {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) :
    dParam p ≠ 4 ∧ dParam p ≠ 6 := by
  constructor
  · intro h
    have hdvd : p ∣ 2 ^ 4 - 1 := by
      have := dvd_two_pow_dParam_sub_one p
      rwa [h] at this
    have h' : p ∣ 15 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 3 * 5 by norm_num at h' ⊢; exact h') with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h'
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).1 h'
      omega
  · intro h
    have hdvd : p ∣ 2 ^ 6 - 1 := by
      have := dvd_two_pow_dParam_sub_one p
      rwa [h] at this
    have h' : p ∣ 63 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 9 * 7 by norm_num at h' ⊢; exact h') with h' | h'
    · rcases (hp.dvd_mul).1 (show p ∣ 3 * 3 by norm_num at h' ⊢; exact h') with h'' | h''
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h''
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h''
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).1 h'
      omega

private theorem prime_eq_of_dvd_two_pow_sub_one {p d : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hd0 : 0 < d) (hd9 : d ≤ 9) (hdvd : p ∣ 2 ^ d - 1) :
    p = 17 ∨ p = 31 ∨ p = 73 ∨ p = 127 := by
  interval_cases d
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have h' : p ∣ 15 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 3 * 5 by norm_num at h' ⊢; exact h') with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h'
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).1 h'
      omega
  · have h' : p ∣ 31 := by norm_num at hdvd ⊢; exact hdvd
    exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp
      (by decide : Nat.Prime 31)).1 h'))
  · have h' : p ∣ 63 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 9 * 7 by norm_num at h' ⊢; exact h') with h' | h'
    · rcases (hp.dvd_mul).1 (show p ∣ 3 * 3 by norm_num at h' ⊢; exact h') with h'' | h''
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h''
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h''
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).1 h'
      omega
  · have h' : p ∣ 127 := by norm_num at hdvd ⊢; exact hdvd
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp
      (by decide : Nat.Prime 127)).1 h')))
  · have h' : p ∣ 255 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 15 * 17 by norm_num at h' ⊢; exact h') with h' | h'
    · rcases (hp.dvd_mul).1 (show p ∣ 3 * 5 by norm_num at h' ⊢; exact h') with h'' | h''
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h''
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).1 h''
        omega
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).1 h')
  · have h' : p ∣ 511 := by norm_num at hdvd ⊢; exact hdvd
    rcases (hp.dvd_mul).1 (show p ∣ 7 * 73 by norm_num at h' ⊢; exact h') with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).1 h'
      omega
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp
        (by decide : Nat.Prime 73)).1 h')))

theorem four_le_dParam {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) : 4 ≤ dParam p := by
  by_contra h
  have hd0 : 0 < dParam p := dParam_pos hp (by omega)
  have hdvd := dvd_two_pow_dParam_sub_one p
  have hpos : 0 < 2 ^ dParam p - 1 := by
    have := Nat.one_lt_two_pow hd0.ne'
    omega
  have hple : p ≤ 2 ^ dParam p - 1 := Nat.le_of_dvd hpos hdvd
  have hle3 : dParam p ≤ 3 := by omega
  have hsmall : 2 ^ dParam p - 1 ≤ 7 := by
    interval_cases dParam p <;> norm_num
  omega

theorem eight_le_dihedralDeg {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) : 8 ≤ dihedralDeg p := by
  have h4 := four_le_dParam hp h11
  have hne := not_dParam_four_six hp h11
  unfold dihedralDeg
  split_ifs with he
  · by_contra h
    have hlt : dParam p < 8 := by omega
    obtain ⟨k, hk⟩ := he
    have hcase : dParam p = 4 ∨ dParam p = 6 := by omega
    rcases hcase with h' | h'
    · exact hne.1 h'
    · exact hne.2 h'
  · omega

theorem ten_le_dParam {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h17 : p ≠ 17) (h31 : p ≠ 31)
    (h73 : p ≠ 73) (h127 : p ≠ 127) : 10 ≤ dParam p := by
  by_contra h
  have hd0 : 0 < dParam p := dParam_pos hp (by omega)
  have hle9 : dParam p ≤ 9 := by omega
  have hdvd := dvd_two_pow_dParam_sub_one p
  rcases prime_eq_of_dvd_two_pow_sub_one hp h11 hd0 hle9 hdvd with h' | h' | h' | h' <;>
    omega

theorem not_two_pow_eq :
    (∀ j : ℕ, (2 : ZMod 31) ^ j ≠ 9) ∧ (∀ j : ℕ, (2 : ZMod 73) ^ j ≠ 9) ∧
      (∀ j : ℕ, (2 : ZMod 127) ^ j ≠ 9) ∧ (∀ j : ℕ, (2 : ZMod 17) ^ j ≠ 3) := by
  have h17 : dParam 17 = 8 := dParam_eq_of_small.2.2.2.1
  have h31 : dParam 31 = 5 := dParam_eq_of_small.2.2.2.2.1
  have h73 : dParam 73 = 9 := dParam_eq_of_small.2.2.2.2.2.1
  have h127 : dParam 127 = 7 := dParam_eq_of_small.2.2.2.2.2.2
  have key : ∀ (p n c : ℕ), dParam p = n → ∀ j : ℕ, (2 : ZMod p) ^ (j % n) ≠ c →
      (2 : ZMod p) ^ j ≠ c := by
    intro p n c hn j hj h
    rw [dParam] at hn
    rw [← pow_mod_orderOf] at h
    rw [hn] at h
    exact hj h
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · refine key 31 5 9 h31 j ?_
    have := Nat.mod_lt j (by norm_num : 0 < 5)
    interval_cases j % 5 <;> decide
  · refine key 73 9 9 h73 j ?_
    have := Nat.mod_lt j (by norm_num : 0 < 9)
    interval_cases j % 9 <;> decide
  · refine key 127 7 9 h127 j ?_
    have := Nat.mod_lt j (by norm_num : 0 < 7)
    interval_cases j % 7 <;> decide
  · refine key 17 8 3 h17 j ?_
    have := Nat.mod_lt j (by norm_num : 0 < 8)
    interval_cases j % 8 <;> decide

theorem sub_one_dvd_pow_sub_one (p e : ℕ) : p - 1 ∣ p ^ e - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow p 1 e

theorem two_mul_sub_one_dvd_pow_sub_one {p e : ℕ} (hp : Odd p) (he : Even e) :
    2 * (p - 1) ∣ p ^ e - 1 := by
  have h2e : 2 ∣ e := even_iff_two_dvd.1 he
  have hsq : p ^ 2 - 1 ∣ p ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one p h2e
  have hfac : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    rw [Nat.sq_sub_sq p 1, mul_comm]
  have h2 : 2 * (p - 1) ∣ (p - 1) * (p + 1) := by
    obtain ⟨m, hm⟩ := hp
    refine ⟨m + 1, ?_⟩
    rw [hm]
    rw [show (2 * m + 1) - 1 = 2 * m by omega]
    ring
  rw [← hfac] at hsq
  exact h2.trans hsq

theorem even_of_isSquare_pow {p e : ℕ} (hp : p.Prime) (h : IsSquare (p ^ e)) : Even e := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := h
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (pow_pos hp.pos e).ne' hm
  have hval := congrArg (padicValNat p) hm
  rw [padicValNat.prime_pow, padicValNat.mul hm0 hm0] at hval
  exact ⟨padicValNat p m, by omega⟩

private theorem le_orbLen_even {p e B : ℕ} (hE : Even e) (hB : B ≤ p ^ e) (_hp : 1 ≤ p) :
    (B - 1) / (2 * (p - 1)) ≤ orbLen p e := by
  rw [orbLen, if_pos hE]
  exact Nat.div_le_div_right (by omega)

private theorem le_orbLen_odd {p e B : ℕ} (hE : ¬ Even e) (hB : B ≤ p ^ e) (_hp : 1 ≤ p) :
    (B - 1) / (p - 1) ≤ orbLen p e := by
  rw [orbLen, if_neg hE]
  exact Nat.div_le_div_right (by omega)

private theorem two_le_orbLen {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 < e) :
    2 ≤ orbLen p e := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have he2 : 2 ≤ e := by omega
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [Nat.sq_sub_sq p 1, mul_comm]
  have hB : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos he2
  have h4 : 4 ≤ p + 1 := by omega
  have hstep : 2 * (2 * (p - 1)) ≤ p ^ 2 - 1 := by
    rw [hfac]
    calc 2 * (2 * (p - 1)) = 4 * (p - 1) := by ring
      _ ≤ (p + 1) * (p - 1) := Nat.mul_le_mul_right _ h4
  by_cases hE : Even e
  · rw [orbLen, if_pos hE, Nat.le_div_iff_mul_le (by omega : 0 < 2 * (p - 1))]
    omega
  · rw [orbLen, if_neg hE, Nat.le_div_iff_mul_le (by omega : 0 < p - 1)]
    have hstep' : 2 * (p - 1) ≤ p ^ 2 - 1 := by
      calc 2 * (p - 1) ≤ 2 * (2 * (p - 1)) :=
            Nat.mul_le_mul_left _ (by omega)
        _ ≤ p ^ 2 - 1 := hstep
    omega

theorem sixteen_le_dihedralDeg_mul_orbLen {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 < e)
    (hq : 9 < p ^ e) (hq25 : p ^ e ≠ 25) : 16 ≤ dihedralDeg p * orbLen p e := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
    by_cases h11 : 11 ≤ p
    · exact Or.inr (Or.inr (Or.inr h11))
    · have hle : p ≤ 10 := by omega
      interval_cases p
      · exact Or.inl rfl
      · exact absurd hp (by decide)
      · exact Or.inr (Or.inl rfl)
      · exact absurd hp (by decide)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
  rcases hcases with rfl | rfl | rfl | h11
  · have he3 : 3 ≤ e := by
      by_contra h
      have hle : e ≤ 2 := by omega
      have hpowe : 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hδ : dihedralDeg 3 = 2 := by
      rw [dihedralDeg, dParam_eq_of_small.1, if_pos (by decide : Even 2)]
    by_cases hE : Even e
    · have he4 : 4 ≤ e := by
        by_contra h
        have heq : e = 3 := by omega
        rw [heq] at hE
        norm_num at hE
      have hB : 3 ^ 4 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he4
      have h8 : 8 ≤ orbLen 3 e := by
        refine le_trans ?_ (le_orbLen_even (p := 3) (B := 3 ^ 4) hE hB (by norm_num))
        norm_num
      calc 16 = 2 * 8 := by norm_num
        _ ≤ dihedralDeg 3 * orbLen 3 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 2 h8
    · have hB : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he3
      have h8 : 8 ≤ orbLen 3 e := by
        refine le_trans ?_ (le_orbLen_odd (p := 3) (B := 3 ^ 3) hE hB (by norm_num))
        norm_num
      calc 16 = 2 * 8 := by norm_num
        _ ≤ dihedralDeg 3 * orbLen 3 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 2 h8
  · have he3 : 3 ≤ e := by
      by_contra h
      have heq : e = 2 := by omega
      rw [heq] at hq25
      norm_num at hq25
    have hδ : dihedralDeg 5 = 4 := by
      rw [dihedralDeg, dParam_eq_of_small.2.1, if_pos (by decide : Even 4)]
    by_cases hE : Even e
    · have he4 : 4 ≤ e := by
        by_contra h
        have heq : e = 3 := by omega
        rw [heq] at hE
        norm_num at hE
      have hB : 5 ^ 4 ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he4
      have h4 : 4 ≤ orbLen 5 e := by
        refine le_trans ?_ (le_orbLen_even (p := 5) (B := 5 ^ 4) hE hB (by norm_num))
        norm_num
      calc 16 = 4 * 4 := by norm_num
        _ ≤ dihedralDeg 5 * orbLen 5 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 4 h4
    · have hB : 5 ^ 3 ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he3
      have h4 : 4 ≤ orbLen 5 e := by
        refine le_trans ?_ (le_orbLen_odd (p := 5) (B := 5 ^ 3) hE hB (by norm_num))
        norm_num
      calc 16 = 4 * 4 := by norm_num
        _ ≤ dihedralDeg 5 * orbLen 5 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 4 h4
  · have he2 : 2 ≤ e := by
      by_contra h
      have hle : e ≤ 1 := by omega
      have hpowe : 7 ^ e ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hδ : dihedralDeg 7 = 6 := by
      rw [dihedralDeg, dParam_eq_of_small.2.2.1, if_neg (by decide : ¬ Even 3)]
    by_cases hE : Even e
    · have hB : 7 ^ 2 ≤ 7 ^ e := Nat.pow_le_pow_right (by norm_num) he2
      have h3 : 3 ≤ orbLen 7 e := by
        refine le_trans ?_ (le_orbLen_even (p := 7) (B := 7 ^ 2) hE hB (by norm_num))
        norm_num
      calc 16 ≤ 6 * 3 := by norm_num
        _ ≤ dihedralDeg 7 * orbLen 7 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 6 h3
    · have he3 : 3 ≤ e := by
        by_contra h
        have heq : e = 2 := by omega
        rw [heq] at hE
        norm_num at hE
      have hB : 7 ^ 3 ≤ 7 ^ e := Nat.pow_le_pow_right (by norm_num) he3
      have h3 : 3 ≤ orbLen 7 e := by
        refine le_trans ?_ (le_orbLen_odd (p := 7) (B := 7 ^ 3) hE hB (by norm_num))
        norm_num
      calc 16 ≤ 6 * 3 := by norm_num
        _ ≤ dihedralDeg 7 * orbLen 7 e := by
              rw [hδ]
              exact Nat.mul_le_mul_left 6 h3
  · have hδ := eight_le_dihedralDeg hp h11
    have h2 := two_le_orbLen hp hp2 he
    calc 16 = 8 * 2 := by norm_num
      _ ≤ dihedralDeg p * orbLen p e := Nat.mul_le_mul hδ h2

theorem dihedralDeg_mul_orbLen_twentyFive : dihedralDeg 5 * orbLen 5 2 = 12 := by
  have hd : dihedralDeg 5 = 4 := by
    rw [dihedralDeg, dParam_eq_of_small.2.1, if_pos (by decide : Even 4)]
  have ho : orbLen 5 2 = 3 := by
    rw [orbLen, if_pos (by decide : Even 2)]
    norm_num
  rw [hd, ho]

theorem orbLen_one {p : ℕ} (hp : p.Prime) : orbLen p 1 = 1 := by
  rw [orbLen, if_neg (by decide : ¬ Even 1), pow_one]
  exact Nat.div_self (by have := hp.two_le; omega)

theorem twentyFour_le_dParam_mul {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 < e)
    (hq : 9 < p ^ e) : 24 ≤ dParam p * ((p ^ e - 1) / (p - 1)) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    rw [Nat.sq_sub_sq p 1, mul_comm]
  have hquot : p + 1 ≤ (p ^ e - 1) / (p - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < p - 1)]
    have hB : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega : 2 ≤ e)
    have hle : (p + 1) * (p - 1) ≤ p ^ e - 1 := by
      rw [← hfac]
      omega
    exact hle
  have hcases3 : p = 3 ∨ 5 ≤ p := by
    by_cases h5 : 5 ≤ p
    · exact Or.inr h5
    · have hle : p ≤ 4 := by omega
      interval_cases p
      · exact Or.inl rfl
      · exact absurd hp (by decide)
  rcases hcases3 with rfl | h5
  · have he3 : 3 ≤ e := by
      by_contra h
      have hle : e ≤ 2 := by omega
      have hpowe : 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hq13 : 13 ≤ (3 ^ e - 1) / (3 - 1) := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3 - 1)]
      have hB : 3 ^ 3 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he3
      norm_num
      omega
    have hd : dParam 3 = 2 := dParam_eq_of_small.1
    rw [hd]
    have h := Nat.mul_le_mul_left 2 (le_trans (by norm_num : 12 ≤ 13) hq13)
    omega
  · have hcases : p = 5 ∨ p = 7 ∨ 11 ≤ p := by
      by_cases h11 : 11 ≤ p
      · exact Or.inr (Or.inr h11)
      · have hle : p ≤ 10 := by omega
        interval_cases p
        · exact Or.inl rfl
        · exact absurd hp (by decide)
        · exact Or.inr (Or.inl rfl)
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
        · exact absurd hp (by decide)
    rcases hcases with rfl | rfl | h11
    · have hd : dParam 5 = 4 := dParam_eq_of_small.2.1
      have h6 : 6 ≤ (5 ^ e - 1) / (5 - 1) := le_trans (by norm_num : 6 ≤ 5 + 1) hquot
      rw [hd]
      have h := Nat.mul_le_mul_left 4 h6
      omega
    · have hd : dParam 7 = 3 := dParam_eq_of_small.2.2.1
      have h8 : 8 ≤ (7 ^ e - 1) / (7 - 1) := le_trans (by norm_num : 8 ≤ 7 + 1) hquot
      rw [hd]
      have h := Nat.mul_le_mul_left 3 h8
      omega
    · have hd := four_le_dParam hp h11
      have hp12 : 12 ≤ p + 1 := by omega
      have h1 : 4 * 12 ≤ dParam p * (p + 1) := Nat.mul_le_mul hd hp12
      have h2 : dParam p * (p + 1) ≤ dParam p * ((p ^ e - 1) / (p - 1)) :=
        Nat.mul_le_mul_left _ hquot
      omega

private theorem field_bracket_eq {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (_hf : 0 < f) :
    (p ^ (2 * f) - 1) / (2 * (p - 1)) - 2 * ((p ^ f - 1) / (p - 1)) =
      ((p ^ f - 1) / (p - 1)) * ((p ^ f - 3) / 2) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrodd : Odd (p ^ f) := hpodd.pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hden : 0 < 2 * (p - 1) := by omega
  have hnum : p ^ (2 * f) - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    have h2f : p ^ (2 * f) = (p ^ f) ^ 2 := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    rw [h2f]
    exact Nat.sq_sub_sq (p ^ f) 1
  have hs : ((p ^ f - 1) / (p - 1)) * (p - 1) = p ^ f - 1 :=
    Nat.div_mul_cancel (sub_one_dvd_pow_sub_one p f)
  obtain ⟨t, ht⟩ : ∃ t, p ^ f + 1 = 2 * t := by
    obtain ⟨k, hk⟩ := hrodd
    exact ⟨k + 1, by omega⟩
  have hA : (p ^ (2 * f) - 1) / (2 * (p - 1)) = ((p ^ f - 1) / (p - 1)) * t := by
    conv_lhs => rw [hnum, ← hs]
    rw [ht]
    rw [show (2 * t) * (((p ^ f - 1) / (p - 1)) * (p - 1))
        = (((p ^ f - 1) / (p - 1)) * t) * (2 * (p - 1)) by ring]
    rw [Nat.mul_div_left _ hden]
  have ht2 : t - 2 = (p ^ f - 3) / 2 := by omega
  rw [hA, ← ht2]
  rw [Nat.mul_sub_left_distrib]
  rw [mul_comm 2 (((p ^ f - 1) / (p - 1)))]

theorem sixteen_le_dParam_mul_field {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 9 ≤ p ^ f) :
    16 ≤ dParam p * ((p ^ (2 * f) - 1) / (2 * (p - 1)) - 2 * ((p ^ f - 1) / (p - 1))) := by
  have hf : 0 < f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst h0
    norm_num at hr
  rw [field_bracket_eq hp hp2 hf]
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ 11 ≤ p := by
    by_cases h11 : 11 ≤ p
    · exact Or.inr (Or.inr (Or.inr h11))
    · have hle : p ≤ 10 := by omega
      interval_cases p
      · exact Or.inl rfl
      · exact absurd hp (by decide)
      · exact Or.inr (Or.inl rfl)
      · exact absurd hp (by decide)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
  rcases hcases with rfl | rfl | rfl | h11
  · have hf2 : 2 ≤ f := by
      by_contra h
      have hle : f ≤ 1 := by omega
      have hpowe : 3 ^ f ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hs : 4 ≤ (3 ^ f - 1) / (3 - 1) := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3 - 1)]
      have hB : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      norm_num
      omega
    have hx : 3 ≤ (3 ^ f - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega
    have hd : dParam 3 = 2 := dParam_eq_of_small.1
    rw [hd]
    have h1 : 2 * 4 ≤ 2 * ((3 ^ f - 1) / (3 - 1)) := Nat.mul_le_mul_left 2 hs
    have h2 : 2 * 4 * 3 ≤ 2 * ((3 ^ f - 1) / (3 - 1)) * ((3 ^ f - 3) / 2) :=
      Nat.mul_le_mul h1 hx
    rw [← mul_assoc]
    omega
  · have hf2 : 2 ≤ f := by
      by_contra h
      have hle : f ≤ 1 := by omega
      have hpowe : 5 ^ f ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hs : 6 ≤ (5 ^ f - 1) / (5 - 1) := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5 - 1)]
      have hB : 5 ^ 2 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      norm_num
      omega
    have hx : 11 ≤ (5 ^ f - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have hB : 5 ^ 2 ≤ 5 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      norm_num
      omega
    have hd : dParam 5 = 4 := dParam_eq_of_small.2.1
    rw [hd]
    have h1 : 4 * 6 ≤ 4 * ((5 ^ f - 1) / (5 - 1)) := Nat.mul_le_mul_left 4 hs
    have h2 : 4 * 6 * 11 ≤ 4 * ((5 ^ f - 1) / (5 - 1)) * ((5 ^ f - 3) / 2) :=
      Nat.mul_le_mul h1 hx
    rw [← mul_assoc]
    omega
  · have hf2 : 2 ≤ f := by
      by_contra h
      have hle : f ≤ 1 := by omega
      have hpowe : 7 ^ f ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
      norm_num at hpowe
      omega
    have hs : 8 ≤ (7 ^ f - 1) / (7 - 1) := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 7 - 1)]
      have hB : 7 ^ 2 ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      norm_num
      omega
    have hx : 23 ≤ (7 ^ f - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      have hB : 7 ^ 2 ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      norm_num
      omega
    have hd : dParam 7 = 3 := dParam_eq_of_small.2.2.1
    rw [hd]
    have h1 : 3 * 8 ≤ 3 * ((7 ^ f - 1) / (7 - 1)) := Nat.mul_le_mul_left 3 hs
    have h2 : 3 * 8 * 23 ≤ 3 * ((7 ^ f - 1) / (7 - 1)) * ((7 ^ f - 3) / 2) :=
      Nat.mul_le_mul h1 hx
    rw [← mul_assoc]
    omega
  · have hd := four_le_dParam hp h11
    have hB : p ≤ p ^ f := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    have hs : 1 ≤ (p ^ f - 1) / (p - 1) := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < p - 1)]
      omega
    have hx : 4 ≤ (p ^ f - 3) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      omega
    have h1 : 4 * 1 ≤ dParam p * ((p ^ f - 1) / (p - 1)) := Nat.mul_le_mul hd hs
    have h2 : 4 * 1 * 4 ≤ dParam p * ((p ^ f - 1) / (p - 1)) * ((p ^ f - 3) / 2) :=
      Nat.mul_le_mul h1 hx
    rw [← mul_assoc]
    omega

theorem field_counts_small :
    (5 ^ (2 * 1) - 1) / (2 * (5 - 1)) = 3 ∧ 2 * ((5 ^ 1 - 1) / (5 - 1)) = 2 ∧
      (7 ^ (2 * 1) - 1) / (2 * (7 - 1)) = 4 ∧ 2 * ((7 ^ 1 - 1) / (7 - 1)) = 2 ∧
      dihedralDeg 7 = 6 := by
  have hd : dihedralDeg 7 = 6 := by
    rw [dihedralDeg, dParam_eq_of_small.2.2.1, if_neg (by decide : ¬ Even 3)]
  norm_num [hd]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour
