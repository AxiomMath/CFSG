module

public import CFSG.Quasithin.Vol2.Ch11SecO7f
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE.C10KH

open CFSG.Open CFSG.Blueprint

theorem odd_pow (m j : ℕ) (hm : 1 ≤ m) (hj : 1 ≤ j) : Odd ((2 ^ m) ^ j - 1) :=
  CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hm hj

theorem match_two {m j A x w : ℕ} (hx : Odd x) (hw : Odd w) (h : (2 ^ m) ^ j * x = 2 ^ A * w) :
    m * j = A ∧ x = w := by
  rw [← pow_mul] at h
  have h1 := SecA.eq_of_two_pow_mul_odd hx hw h
  refine ⟨h1, ?_⟩
  rw [h1] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem not_list701Excl_of_profile {Y : Type} [Group Y] {A w : ℕ} (hY : Nat.card Y = 2 ^ A * w)
    (hw : Odd w) (hA : 11 ≤ A) (h1 : w ≠ (2 ^ A) ^ 2 - 1)
    (h2 : ∀ m, m * 3 = A → w ≠ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1))
    (h3 : ∀ m, m * 4 = A → w ≠ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))
    (h4 : ∀ m, m * 6 = A → w ≠ ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) : ¬ List701Excl Y := by
  have hw1 : 1 ≤ w := hw.pos
  have h11 : 2 ^ 11 ∣ 2 ^ A * w := (Nat.pow_dvd_pow 2 hA).trans (dvd_mul_right _ _)
  have hpos : 0 < 2 ^ A * w := by positivity
  refine not_list701Excl_of hY (fun m h => ?_) (fun m h => ?_) (fun m h => ?_) (fun m h => ?_)
    (fun h => ?_) ?_ ?_
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · obtain ⟨hmA, hx⟩ := match_two (j := 1) (odd_pow m 2 hm (by norm_num)) hw (by simpa using h)
      rw [mul_one] at hmA
      subst hmA
      exact h1 hx.symm
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · obtain ⟨hmA, hx⟩ := match_two ((odd_pow m 2 hm (by norm_num)).mul
        (odd_pow m 3 hm (by norm_num))) hw h
      exact h2 m hmA hx.symm
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · obtain ⟨hmA, hx⟩ := match_two ((odd_pow m 2 hm (by norm_num)).mul
        (odd_pow m 4 hm (by norm_num))) hw h
      exact h3 m hmA hx.symm
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h
      omega
    · obtain ⟨hmA, hx⟩ := match_two ((odd_pow m 6 hm (by norm_num)).mul
        (odd_pow m 2 hm (by norm_num))) hw h
      exact h4 m hmA hx.symm
  · have := h11.trans h
    norm_num at this
  · have : 2 ^ 11 ≤ 2 ^ A * w := Nat.le_of_dvd hpos h11
    omega
  · refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_⟩ <;> rw [h] at h11 <;> norm_num at h11

theorem triality_odd_lt {s : ℕ} (hs : 2 ≤ s) :
    (s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)) < (s ^ 12) ^ 2 - 1 ∧
      (s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)) < (s ^ 8 - 1) * (s ^ 12 - 1) ∧
      (s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)) < (s ^ 6 - 1) * (s ^ 12 - 1) ∧
      (s ^ 8 + s ^ 4 + 1) * ((s ^ 6 - 1) * (s ^ 2 - 1)) < (s ^ 12 - 1) * (s ^ 4 - 1) := by
  have h2 : 4 ≤ s ^ 2 := by nlinarith
  have h4 : 16 ≤ s ^ 4 := by nlinarith
  have h6 : 64 ≤ s ^ 6 := by nlinarith
  have h8 : 256 ≤ s ^ 8 := by nlinarith
  have h12 : 4096 ≤ s ^ 12 := by nlinarith
  have e4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have e6 : s ^ 6 = s ^ 2 * s ^ 4 := by ring
  have e8 : s ^ 8 = s ^ 4 * s ^ 4 := by ring
  have e12 : s ^ 12 = s ^ 4 * s ^ 8 := by ring
  zify [show 1 ≤ s ^ 2 by omega, show 1 ≤ s ^ 4 by omega, show 1 ≤ s ^ 6 by omega,
    show 1 ≤ s ^ 8 by omega, show 1 ≤ s ^ 12 by omega,
    show 1 ≤ (s ^ 12) ^ 2 by nlinarith]
  set a : ℤ := (s : ℤ) ^ 2 with ha
  have ha4 : (4 : ℤ) ≤ a := by rw [ha]; exact_mod_cast h2
  have hs4 : (s : ℤ) ^ 4 = a ^ 2 := by rw [ha]; ring
  have hs6 : (s : ℤ) ^ 6 = a ^ 3 := by rw [ha]; ring
  have hs8 : (s : ℤ) ^ 8 = a ^ 4 := by rw [ha]; ring
  have hs12 : (s : ℤ) ^ 12 = a ^ 6 := by rw [ha]; ring
  rw [hs4, hs6, hs8, hs12]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_pos (by linarith : (0 : ℤ) < a)
    (by nlinarith : (0 : ℤ) < (a - 1) ^ 2), pow_pos (by linarith : (0 : ℤ) < a) 5,
    pow_pos (by linarith : (0 : ℤ) < a) 7, pow_pos (by linarith : (0 : ℤ) < a) 9,
    pow_pos (by linarith : (0 : ℤ) < a) 11]

theorem twistedF4_odd_lt {s : ℕ} (hs : 2 ≤ s) :
    (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) < (s ^ 12) ^ 2 - 1 ∧
      (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) < (s ^ 8 - 1) * (s ^ 12 - 1) ∧
      (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) < (s ^ 6 - 1) * (s ^ 12 - 1) ∧
      (s ^ 6 + 1) * (s ^ 4 - 1) * (s ^ 3 + 1) * (s - 1) < (s ^ 12 - 1) * (s ^ 4 - 1) := by
  have h4 : 2 ^ 4 ≤ s ^ 4 := Nat.pow_le_pow_left hs 4
  have h6 : 2 ^ 6 ≤ s ^ 6 := Nat.pow_le_pow_left hs 6
  have h8 : 2 ^ 8 ≤ s ^ 8 := Nat.pow_le_pow_left hs 8
  have h12 : 2 ^ 12 ≤ s ^ 12 := Nat.pow_le_pow_left hs 12
  norm_num at h4 h6 h8 h12
  zify [show 1 ≤ s by omega, show 1 ≤ s ^ 4 by omega, show 1 ≤ s ^ 6 by omega,
    show 1 ≤ s ^ 8 by omega, show 1 ≤ s ^ 12 by omega, show 1 ≤ (s ^ 12) ^ 2 by nlinarith]
  have hs2 : (2 : ℤ) ≤ s := by exact_mod_cast hs
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [pow_pos (by linarith : (0 : ℤ) < s) 3,
    pow_pos (by linarith : (0 : ℤ) < s) 5, pow_pos (by linarith : (0 : ℤ) < s) 7,
    pow_pos (by linarith : (0 : ℤ) < s) 9, pow_pos (by linarith : (0 : ℤ) < s) 11,
    pow_pos (by linarith : (0 : ℤ) < s) 13, pow_pos (by linarith : (0 : ℤ) < s) 15,
    pow_pos (by linarith : (0 : ℤ) < s) 17, pow_pos (by linarith : (0 : ℤ) < s) 19,
    pow_pos (by linarith : (0 : ℤ) < s) 21, pow_pos (by linarith : (0 : ℤ) < s) 23]

end CFSG.Quasithin.Vol2.Ch11.SecE.C10KH
