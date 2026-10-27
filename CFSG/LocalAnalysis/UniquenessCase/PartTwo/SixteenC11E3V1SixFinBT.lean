module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixFinBF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv

@[expose] def sixCodeTab (c : s1611e3_SixCode) : Nat :=
  if c.eps then
    (6 + (c.sigma 0).val) ||| ((6 + (c.sigma 1).val) <<< 4) ||| ((6 + (c.sigma 2).val) <<< 8) |||
    ((6 + (c.sigma 3).val) <<< 12) ||| ((6 + (c.sigma 4).val) <<< 16) |||
    ((6 + (c.sigma 5).val) <<< 20) ||| ((c.tau 0).val <<< 24) ||| ((c.tau 1).val <<< 28) |||
    ((c.tau 2).val <<< 32) ||| ((c.tau 3).val <<< 36) ||| ((c.tau 4).val <<< 40) |||
    ((c.tau 5).val <<< 44)
  else
    (c.sigma 0).val ||| ((c.sigma 1).val <<< 4) ||| ((c.sigma 2).val <<< 8) |||
    ((c.sigma 3).val <<< 12) ||| ((c.sigma 4).val <<< 16) ||| ((c.sigma 5).val <<< 20) |||
    ((6 + (c.tau 0).val) <<< 24) ||| ((6 + (c.tau 1).val) <<< 28) |||
    ((6 + (c.tau 2).val) <<< 32) ||| ((6 + (c.tau 3).val) <<< 36) |||
    ((6 + (c.tau 4).val) <<< 40) ||| ((6 + (c.tau 5).val) <<< 44)

private def s1611e3_sixDest (c : s1611e3_SixCode) (j : Nat) : Nat :=
  if j < 6 then
    (if c.eps then 6 else 0) + (c.sigma ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val
  else
    (if c.eps then 0 else 6) + (c.tau ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val

private theorem s1611e3_sixDest_lt (c : s1611e3_SixCode) (j : Nat) :
    s1611e3_sixDest c j < 12 := by
  have h1 : (c.sigma ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
    (c.sigma ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
  have h2 : (c.tau ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
    (c.tau ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
  unfold s1611e3_sixDest
  split <;> split <;> omega

private theorem s1611e3_sixDest_low (c : s1611e3_SixCode) {j : Nat} (hj : j < 6) :
    s1611e3_sixDest c j = (if c.eps then 6 else 0) + (c.sigma ⟨j, hj⟩).val := by
  have hfin : (⟨j % 6, Nat.mod_lt j (by norm_num)⟩ : Fin 6) = ⟨j, hj⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hj)
  unfold s1611e3_sixDest
  rw [if_pos hj, hfin]

private theorem s1611e3_sixDest_high (c : s1611e3_SixCode) {j : Nat} (hj : ¬ j < 6) :
    s1611e3_sixDest c j =
      (if c.eps then 0 else 6) + (c.tau ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val := by
  unfold s1611e3_sixDest
  rw [if_neg hj]

private theorem s1611e3_sixDest_mul (c d : s1611e3_SixCode) {j : Nat} (hj : j < 12) :
    s1611e3_sixDest (s1611e3_sixCodeMul c d) j = s1611e3_sixDest c (s1611e3_sixDest d j) := by
  obtain ⟨σ1, τ1, ε1⟩ := c
  obtain ⟨σ2, τ2, ε2⟩ := d
  by_cases hj6 : j < 6
  · cases ε1 <;> cases ε2 <;>
      simp only [s1611e3_sixCodeMul, Bool.false_eq_true, if_true, if_false, reduceIte]
    · rw [s1611e3_sixDest_low (⟨σ1 * σ2, τ1 * τ2, false⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_low (⟨σ2, τ2, false⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_false, reduceIte, Nat.zero_add]
      have hdl : (σ2 ⟨j, hj6⟩).val < 6 := (σ2 ⟨j, hj6⟩).isLt
      rw [s1611e3_sixDest_low (⟨σ1, τ1, false⟩ : s1611e3_SixCode) hdl]
      simp only [Bool.false_eq_true, if_false, reduceIte, Nat.zero_add]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_low (⟨τ1 * σ2, σ1 * τ2, true⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_low (⟨σ2, τ2, true⟩ : s1611e3_SixCode) hj6]
      simp only [if_true, reduceIte]
      have hv : (σ2 ⟨j, hj6⟩).val < 6 := (σ2 ⟨j, hj6⟩).isLt
      have hdge : ¬ (6 + (σ2 ⟨j, hj6⟩).val < 6) := by omega
      rw [s1611e3_sixDest_high (⟨σ1, τ1, false⟩ : s1611e3_SixCode) hdge]
      simp only [Bool.false_eq_true, if_false, reduceIte]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_low (⟨σ1 * σ2, τ1 * τ2, true⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_low (⟨σ2, τ2, false⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_true, if_false, reduceIte, Nat.zero_add]
      have hdl : (σ2 ⟨j, hj6⟩).val < 6 := (σ2 ⟨j, hj6⟩).isLt
      rw [s1611e3_sixDest_low (⟨σ1, τ1, true⟩ : s1611e3_SixCode) hdl]
      simp only [if_true, reduceIte]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_low (⟨τ1 * σ2, σ1 * τ2, false⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_low (⟨σ2, τ2, true⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_true, if_false, reduceIte]
      have hv : (σ2 ⟨j, hj6⟩).val < 6 := (σ2 ⟨j, hj6⟩).isLt
      have hdge : ¬ (6 + (σ2 ⟨j, hj6⟩).val < 6) := by omega
      rw [s1611e3_sixDest_high (⟨σ1, τ1, true⟩ : s1611e3_SixCode) hdge]
      simp only [if_true, reduceIte, Nat.zero_add]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
  · cases ε1 <;> cases ε2 <;>
      simp only [s1611e3_sixCodeMul, Bool.false_eq_true, if_true, if_false, reduceIte]
    · rw [s1611e3_sixDest_high (⟨σ1 * σ2, τ1 * τ2, false⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_high (⟨σ2, τ2, false⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_false, reduceIte]
      have hv : (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
        (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
      have hdge : ¬ (6 + (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6) := by omega
      rw [s1611e3_sixDest_high (⟨σ1, τ1, false⟩ : s1611e3_SixCode) hdge]
      simp only [Bool.false_eq_true, if_false, reduceIte]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_high (⟨τ1 * σ2, σ1 * τ2, true⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_high (⟨σ2, τ2, true⟩ : s1611e3_SixCode) hj6]
      simp only [if_true, reduceIte, Nat.zero_add]
      have hdl : (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
        (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
      rw [s1611e3_sixDest_low (⟨σ1, τ1, false⟩ : s1611e3_SixCode) hdl]
      simp only [Bool.false_eq_true, if_false, reduceIte, Nat.zero_add]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_high (⟨σ1 * σ2, τ1 * τ2, true⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_high (⟨σ2, τ2, false⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_true, if_false, reduceIte, Nat.zero_add]
      have hv : (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
        (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
      have hdge : ¬ (6 + (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6) := by omega
      rw [s1611e3_sixDest_high (⟨σ1, τ1, true⟩ : s1611e3_SixCode) hdge]
      simp only [if_true, reduceIte, Nat.zero_add]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega
    · rw [s1611e3_sixDest_high (⟨τ1 * σ2, σ1 * τ2, false⟩ : s1611e3_SixCode) hj6,
          s1611e3_sixDest_high (⟨σ2, τ2, true⟩ : s1611e3_SixCode) hj6]
      simp only [Bool.false_eq_true, if_true, if_false, reduceIte, Nat.zero_add]
      have hdl : (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).val < 6 :=
        (τ2 ⟨j % 6, Nat.mod_lt j (by norm_num)⟩).isLt
      rw [s1611e3_sixDest_low (⟨σ1, τ1, true⟩ : s1611e3_SixCode) hdl]
      simp only [if_true, reduceIte]
      all_goals
        try simp only [Equiv.Perm.mul_apply]
        try rw [Nat.add_right_inj]
        try apply congrArg Fin.val
        try congr 1
        try apply Fin.ext
        try simp only [Fin.val_mk]
        try omega

private theorem s1611e3_eps_eq_of_sixDest (c d : s1611e3_SixCode)
    (h : s1611e3_sixDest c 0 = s1611e3_sixDest d 0) : c.eps = d.eps := by
  obtain ⟨σ1, τ1, ε1⟩ := c
  obtain ⟨σ2, τ2, ε2⟩ := d
  cases ε1 <;> cases ε2 <;> try rfl
  · exfalso
    have h1 : s1611e3_sixDest (⟨σ1, τ1, false⟩ : s1611e3_SixCode) 0 < 6 := by
      rw [s1611e3_sixDest_low (⟨σ1, τ1, false⟩ : s1611e3_SixCode) (by norm_num)]
      simp only [Bool.false_eq_true, if_false, reduceIte, Nat.zero_add]
      exact (σ1 (0 : Fin 6)).isLt
    have h2 : ¬ s1611e3_sixDest (⟨σ2, τ2, true⟩ : s1611e3_SixCode) 0 < 6 := by
      rw [s1611e3_sixDest_low (⟨σ2, τ2, true⟩ : s1611e3_SixCode) (by norm_num)]
      simp only [if_true]
      have := (σ2 (0 : Fin 6)).isLt
      omega
    omega
  · exfalso
    have h2 : s1611e3_sixDest (⟨σ2, τ2, false⟩ : s1611e3_SixCode) 0 < 6 := by
      rw [s1611e3_sixDest_low (⟨σ2, τ2, false⟩ : s1611e3_SixCode) (by norm_num)]
      simp only [Bool.false_eq_true, if_false, reduceIte, Nat.zero_add]
      exact (σ2 (0 : Fin 6)).isLt
    have h1 : ¬ s1611e3_sixDest (⟨σ1, τ1, true⟩ : s1611e3_SixCode) 0 < 6 := by
      rw [s1611e3_sixDest_low (⟨σ1, τ1, true⟩ : s1611e3_SixCode) (by norm_num)]
      simp only [if_true]
      have := (σ1 (0 : Fin 6)).isLt
      omega
    omega

private theorem s1611e3_sixDest_sigma (c : s1611e3_SixCode) (i : Fin 6) :
    (c.sigma i).val = s1611e3_sixDest c i.val - (if c.eps then 6 else 0) := by
  have hi : i.val < 6 := i.isLt
  have hfin : (⟨i.val, hi⟩ : Fin 6) = i := rfl
  rw [s1611e3_sixDest_low c hi, hfin]
  omega

private theorem s1611e3_sixDest_tau (c : s1611e3_SixCode) (i : Fin 6) :
    (c.tau i).val = s1611e3_sixDest c (i.val + 6) - (if c.eps then 0 else 6) := by
  have hi : ¬ i.val + 6 < 6 := by omega
  have hmod : (i.val + 6) % 6 = i.val := by omega
  have hfin : (⟨(i.val + 6) % 6, Nat.mod_lt (i.val + 6) (by norm_num)⟩ : Fin 6) = i :=
    Fin.ext hmod
  rw [s1611e3_sixDest_high c hi, hfin]
  omega

private def s1611e3_orShift (a : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| (a i <<< (4 * i))) 0

private theorem s1611e3_range12 :
    List.range 12 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide

private theorem s1611e3_orShift_succ (a : Nat → Nat) (n : Nat) :
    s1611e3_orShift a (n + 1) = s1611e3_orShift a n ||| (a n <<< (4 * n)) := by
  unfold s1611e3_orShift
  rw [List.range_succ, List.foldl_append]
  simp

private theorem s1611e3_orShift_lt (a : Nat → Nat) (n : Nat)
    (ha : ∀ i, i < n → a i < 16) : s1611e3_orShift a n < 2 ^ (4 * n) := by
  induction n with
  | zero => simp [s1611e3_orShift]
  | succ k ih =>
    rw [s1611e3_orShift_succ]
    have h1 : s1611e3_orShift a k < 2 ^ (4 * (k + 1)) := by
      have := ih (fun i hi => ha i (Nat.lt_succ_of_lt hi))
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega))
    have h2 : a k <<< (4 * k) < 2 ^ (4 * (k + 1)) := by
      rw [Nat.shiftLeft_eq]
      have hlt := ha k (Nat.lt_succ_self k)
      calc a k * 2 ^ (4 * k) < 16 * 2 ^ (4 * k) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
        _ = 2 ^ (4 * (k + 1)) := by
            rw [show (16 : Nat) = 2 ^ 4 by norm_num, ← Nat.pow_add]
            congr 1
            ring
    exact Nat.or_lt_two_pow h1 h2

private theorem s1611e3_orShift_testBit (a : Nat → Nat) (n : Nat)
    (ha : ∀ i, i < n → a i < 16) (j p : Nat) (hj : j < n) (hp : p < 4) :
    (s1611e3_orShift a n).testBit (4 * j + p) = (a j).testBit p := by
  revert ha hj
  induction n with
  | zero => intro ha hj; omega
  | succ k ih =>
    intro ha hj
    rw [s1611e3_orShift_succ, Nat.testBit_or]
    have ha' : ∀ i, i < k → a i < 16 := fun i hi => ha i (Nat.lt_succ_of_lt hi)
    by_cases hjk : j < k
    · have h1 := ih ha' hjk
      have h2 : (a k <<< (4 * k)).testBit (4 * j + p) = false := by
        rw [Nat.testBit_shiftLeft]
        have hlt : ¬ (4 * j + p ≥ 4 * k) := by omega
        simp only [hlt, decide_false, Bool.false_and]
      rw [h1, h2]
      simp
    · have hjeq : j = k := by omega
      rw [hjeq]
      have hlt := s1611e3_orShift_lt a k ha'
      have hle : (2 : Nat) ^ (4 * k) ≤ 2 ^ (4 * k + p) :=
        Nat.pow_le_pow_right (i := 4 * k) (j := 4 * k + p) (by norm_num) (by omega)
      have h1 : (s1611e3_orShift a k).testBit (4 * k + p) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hle)
      have h2 : (a k <<< (4 * k)).testBit (4 * k + p) = (a k).testBit p := by
        rw [Nat.testBit_shiftLeft]
        have hge : 4 * k + p ≥ 4 * k := by omega
        simp only [hge, decide_true, Bool.true_and]
        rw [show (4 * k + p) - 4 * k = p by omega]
      rw [h1, h2]
      simp

private theorem s1611e3_tab_eq_orShift (c : s1611e3_SixCode) :
    sixCodeTab c = s1611e3_orShift (s1611e3_sixDest c) 12 := by
  obtain ⟨σ, τ, ε⟩ := c
  cases ε <;>
    simp [sixCodeTab, s1611e3_orShift, s1611e3_range12, s1611e3_sixDest, List.foldl_cons,
      List.foldl_nil, Nat.zero_or, Nat.shiftLeft_zero, Nat.zero_add, Nat.mod_eq_of_lt]

private theorem s1611e3_testBit_sixTabDigit (t j p : Nat) :
    (sixTabDigit t j).testBit p = (decide (p < 4) && t.testBit (4 * j + p)) := by
  unfold sixTabDigit
  rw [show (15 : Nat) = 2 ^ 4 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

private theorem s1611e3_sixTabDigit_sixCodeTab (c : s1611e3_SixCode) (j : Nat) (hj : j < 12) :
    sixTabDigit (sixCodeTab c) j = s1611e3_sixDest c j := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [s1611e3_testBit_sixTabDigit]
  by_cases hp : p < 4
  · simp only [hp, decide_true, Bool.and_true]
    rw [s1611e3_tab_eq_orShift]
    exact s1611e3_orShift_testBit (s1611e3_sixDest c) 12
      (fun i _ => by have := s1611e3_sixDest_lt c i; omega) j p hj hp
  · simp only [hp, decide_false, Bool.false_and]
    have hlt := s1611e3_sixDest_lt c j
    have : s1611e3_sixDest c j < 2 ^ p := by
      have : (2 : Nat) ^ 4 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega)
      omega
    exact (Nat.testBit_lt_two_pow this).symm

private theorem s1611e3_sixTabDigit_lt (t j : Nat) : sixTabDigit t j < 16 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

private theorem s1611e3_tab_ext (a b : Nat) (ha : a < 2 ^ 48) (hb : b < 2 ^ 48)
    (h : ∀ j, j < 12 → sixTabDigit a j = sixTabDigit b j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 48
  · have hj : k / 4 < 12 := by omega
    have hp : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hk4 : 4 * (k / 4) + k % 4 = k := by omega
    have hka : (sixTabDigit a (k / 4)).testBit (k % 4) = a.testBit k := by
      rw [s1611e3_testBit_sixTabDigit, hk4]
      simp [hp]
    have hkb : (sixTabDigit b (k / 4)).testBit (k % 4) = b.testBit k := by
      rw [s1611e3_testBit_sixTabDigit, hk4]
      simp [hp]
    rw [← hka, ← hkb, h (k / 4) hj]
  · have h1 : a < 2 ^ k :=
      lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega))
    have h2 : b < 2 ^ k :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

private theorem s1611e3_sixCodeTab_lt (c : s1611e3_SixCode) : sixCodeTab c < 2 ^ 48 := by
  rw [s1611e3_tab_eq_orShift]
  have := s1611e3_orShift_lt (s1611e3_sixDest c) 12
    (fun i _ => by have := s1611e3_sixDest_lt c i; omega)
  simpa using this

private theorem s1611e3_tabComp_eq_orShift (a b : Nat) :
    sixTabComp a b = s1611e3_orShift (fun j => sixTabDigit a (sixTabDigit b j)) 12 := by
  simp [sixTabComp, s1611e3_orShift, s1611e3_range12, List.foldl_cons, List.foldl_nil,
    Nat.zero_or, Nat.shiftLeft_zero]

private theorem s1611e3_sixTabDigit_tabComp (a b : Nat) (j : Nat) (hj : j < 12) :
    sixTabDigit (sixTabComp a b) j = sixTabDigit a (sixTabDigit b j) := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [s1611e3_testBit_sixTabDigit]
  by_cases hp : p < 4
  · simp only [hp, decide_true, Bool.and_true]
    rw [s1611e3_tabComp_eq_orShift]
    exact s1611e3_orShift_testBit (fun i => sixTabDigit a (sixTabDigit b i)) 12
      (fun i _ => s1611e3_sixTabDigit_lt a (sixTabDigit b i)) j p hj hp
  · simp only [hp, decide_false, Bool.false_and]
    have hlt := s1611e3_sixTabDigit_lt a (sixTabDigit b j)
    have : sixTabDigit a (sixTabDigit b j) < 2 ^ p := by
      have : (2 : Nat) ^ 4 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega)
      omega
    exact (Nat.testBit_lt_two_pow this).symm

private theorem s1611e3_imgShift (σ : Perm (Fin 6)) (s : Nat) (hs : s = 0 ∨ s = 6) (x : Fin 64) :
    ((((x.val >>> 0) &&& 1) <<< (s + (σ 0).val)) |||
     (((x.val >>> 1) &&& 1) <<< (s + (σ 1).val)) |||
     (((x.val >>> 2) &&& 1) <<< (s + (σ 2).val)) |||
     (((x.val >>> 3) &&& 1) <<< (s + (σ 3).val)) |||
     (((x.val >>> 4) &&& 1) <<< (s + (σ 4).val)) |||
     (((x.val >>> 5) &&& 1) <<< (s + (σ 5).val))) =
      s1611e3_sixBitAct σ x.val <<< s := by
  unfold s1611e3_sixBitAct
  rw [Fin.sum_univ_six]
  rcases hs with rfl | rfl
  · simp only [Nat.zero_add, Nat.shiftLeft_zero]
    revert σ x
    decide +kernel
  · revert σ x
    decide +kernel

private theorem s1611e3_sixTabImg_digits (c : s1611e3_SixCode) (off h : Nat)
    (hoff : off + 6 ≤ 12) :
    sixTabImg (sixCodeTab c) off h =
      (((h >>> 0) &&& 1) <<< s1611e3_sixDest c off) |||
      (((h >>> 1) &&& 1) <<< s1611e3_sixDest c (off + 1)) |||
      (((h >>> 2) &&& 1) <<< s1611e3_sixDest c (off + 2)) |||
      (((h >>> 3) &&& 1) <<< s1611e3_sixDest c (off + 3)) |||
      (((h >>> 4) &&& 1) <<< s1611e3_sixDest c (off + 4)) |||
      (((h >>> 5) &&& 1) <<< s1611e3_sixDest c (off + 5)) := by
  unfold sixTabImg
  rw [s1611e3_sixTabDigit_sixCodeTab c off (by omega),
      s1611e3_sixTabDigit_sixCodeTab c (off + 1) (by omega),
      s1611e3_sixTabDigit_sixCodeTab c (off + 2) (by omega),
      s1611e3_sixTabDigit_sixCodeTab c (off + 3) (by omega),
      s1611e3_sixTabDigit_sixCodeTab c (off + 4) (by omega),
      s1611e3_sixTabDigit_sixCodeTab c (off + 5) (by omega)]

private theorem s1611e3_sixTabImg_lt (t off h : Nat)
    (hd : ∀ k, k < 6 → sixTabDigit t (off + k) < 12) : sixTabImg t off h < 4096 := by
  have hterm : ∀ k, k < 6 → (((h >>> k) &&& 1) <<< sixTabDigit t (off + k)) < 2 ^ 12 := by
    intro k hk
    have hd' := hd k hk
    have hb : ((h >>> k) &&& 1) ≤ 1 := Nat.and_le_right
    calc ((h >>> k) &&& 1) <<< sixTabDigit t (off + k)
        ≤ 1 <<< sixTabDigit t (off + k) := by
          rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
          exact Nat.mul_le_mul_right _ hb
      _ = 2 ^ sixTabDigit t (off + k) := by rw [Nat.shiftLeft_eq, one_mul]
      _ < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) hd'
  rw [show (4096 : Nat) = 2 ^ 12 by norm_num]
  unfold sixTabImg
  exact Nat.or_lt_two_pow
    (Nat.or_lt_two_pow
      (Nat.or_lt_two_pow
        (Nat.or_lt_two_pow
          (Nat.or_lt_two_pow (hterm 0 (by norm_num)) (hterm 1 (by norm_num)))
          (hterm 2 (by norm_num)))
        (hterm 3 (by norm_num)))
      (hterm 4 (by norm_num)))
    (hterm 5 (by norm_num))

private theorem s1611e3_sixTabImg_zero_eq (c : s1611e3_SixCode) (x : Nat) (hx : x < 64) :
    sixTabImg (sixCodeTab c) 0 x =
      (if c.eps then s1611e3_sixBitAct c.sigma x <<< 6 else s1611e3_sixBitAct c.sigma x) := by
  rw [s1611e3_sixTabImg_digits c 0 x (by norm_num)]
  by_cases hc : c.eps = true
  · rw [if_pos hc]
    simpa [s1611e3_sixDest, hc] using s1611e3_imgShift c.sigma 6 (Or.inr rfl) (⟨x, hx⟩ : Fin 64)
  · rw [if_neg hc]
    simpa [s1611e3_sixDest, hc] using s1611e3_imgShift c.sigma 0 (Or.inl rfl) (⟨x, hx⟩ : Fin 64)

private theorem s1611e3_sixTabImg_six_eq (c : s1611e3_SixCode) (x : Nat) (hx : x < 64) :
    sixTabImg (sixCodeTab c) 6 x =
      (if c.eps then s1611e3_sixBitAct c.tau x else s1611e3_sixBitAct c.tau x <<< 6) := by
  rw [s1611e3_sixTabImg_digits c 6 x (by norm_num)]
  by_cases hc : c.eps = true
  · rw [if_pos hc]
    simpa [s1611e3_sixDest, hc] using s1611e3_imgShift c.tau 0 (Or.inl rfl) (⟨x, hx⟩ : Fin 64)
  · rw [if_neg hc]
    simpa [s1611e3_sixDest, hc] using s1611e3_imgShift c.tau 6 (Or.inr rfl) (⟨x, hx⟩ : Fin 64)

private def s1611e3_pack (a : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| (a i <<< (12 * i))) 0

private theorem s1611e3_pack_succ (a : Nat → Nat) (n : Nat) :
    s1611e3_pack a (n + 1) = s1611e3_pack a n ||| (a n <<< (12 * n)) := by
  unfold s1611e3_pack
  rw [List.range_succ, List.foldl_append]
  simp

private theorem s1611e3_pack_lt (a : Nat → Nat) (n : Nat)
    (ha : ∀ i, i < n → a i < 4096) : s1611e3_pack a n < 2 ^ (12 * n) := by
  induction n with
  | zero => simp [s1611e3_pack]
  | succ k ih =>
    rw [s1611e3_pack_succ]
    have h1 : s1611e3_pack a k < 2 ^ (12 * (k + 1)) := by
      have := ih (fun i hi => ha i (Nat.lt_succ_of_lt hi))
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega))
    have h2 : a k <<< (12 * k) < 2 ^ (12 * (k + 1)) := by
      rw [Nat.shiftLeft_eq]
      have hlt := ha k (Nat.lt_succ_self k)
      calc a k * 2 ^ (12 * k) < 4096 * 2 ^ (12 * k) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
        _ = 2 ^ (12 * (k + 1)) := by
            rw [show (4096 : Nat) = 2 ^ 12 by norm_num, ← Nat.pow_add]
            congr 1
            ring
    exact Nat.or_lt_two_pow h1 h2

private theorem s1611e3_pack_testBit (a : Nat → Nat) (n : Nat)
    (ha : ∀ i, i < n → a i < 4096) (j p : Nat) (hj : j < n) (hp : p < 12) :
    (s1611e3_pack a n).testBit (12 * j + p) = (a j).testBit p := by
  revert ha hj
  induction n with
  | zero => intro ha hj; omega
  | succ k ih =>
    intro ha hj
    rw [s1611e3_pack_succ, Nat.testBit_or]
    have ha' : ∀ i, i < k → a i < 4096 := fun i hi => ha i (Nat.lt_succ_of_lt hi)
    by_cases hjk : j < k
    · have h1 := ih ha' hjk
      have h2 : (a k <<< (12 * k)).testBit (12 * j + p) = false := by
        rw [Nat.testBit_shiftLeft]
        have hlt : ¬ (12 * j + p ≥ 12 * k) := by omega
        simp only [hlt, decide_false, Bool.false_and]
      rw [h1, h2]
      simp
    · have hjeq : j = k := by omega
      rw [hjeq]
      have hlt := s1611e3_pack_lt a k ha'
      have hle : (2 : Nat) ^ (12 * k) ≤ 2 ^ (12 * k + p) :=
        Nat.pow_le_pow_right (i := 12 * k) (j := 12 * k + p) (by norm_num) (by omega)
      have h1 : (s1611e3_pack a k).testBit (12 * k + p) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hle)
      have h2 : (a k <<< (12 * k)).testBit (12 * k + p) = (a k).testBit p := by
        rw [Nat.testBit_shiftLeft]
        have hge : 12 * k + p ≥ 12 * k := by omega
        simp only [hge, decide_true, Bool.true_and]
        rw [show (12 * k + p) - 12 * k = p by omega]
      rw [h1, h2]
      simp

private theorem s1611e3_pack_extract (a : Nat → Nat) (ha : ∀ i, i < 64 → a i < 4096)
    (x : Nat) (hx : x < 64) :
    (s1611e3_pack a 64 >>> (12 * x)) &&& 4095 = a x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · rw [Nat.testBit_land, Nat.testBit_shiftRight]
    have h4095 : (4095 : Nat).testBit i = true := by
      rw [show (4095 : Nat) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [hi]
    rw [h4095, Bool.and_true]
    exact s1611e3_pack_testBit a 64 ha x i hx hi
  · rw [Nat.testBit_land, Nat.testBit_shiftRight]
    have h4095 : (4095 : Nat).testBit i = false := by
      rw [show (4095 : Nat) = 2 ^ 12 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp [hi]
    rw [h4095, Bool.and_false]
    have hlt := ha x hx
    have : a x < 2 ^ i := by
      have : (2 : Nat) ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num : (0 : Nat) < 2) (by omega)
      omega
    exact (Nat.testBit_lt_two_pow this).symm

private theorem s1611e3_bitSum_testBit (c : Fin 6 → Bool) (p : Fin 6) :
    (∑ i : Fin 6, (if c i then 1 else 0) * 2 ^ (i : Nat)).testBit (p : Nat) = c p := by
  rw [Fin.sum_univ_six]
  revert c p
  decide +kernel

private theorem s1611e3_sixBitAct_testBit (σ : Perm (Fin 6)) (x : Nat) (p : Fin 6) :
    (s1611e3_sixBitAct σ x).testBit (p : Nat) =
      (((x >>> ((σ⁻¹ p : Fin 6) : Nat)) &&& 1) == 1) := by
  set c : Fin 6 → Bool := fun i => (x >>> ((Equiv.symm σ i : Fin 6) : Nat)) % 2 == 1
  have hsum : s1611e3_sixBitAct σ x =
      ∑ i : Fin 6, (if c i then 1 else 0) * 2 ^ (i : Nat) := by
    unfold s1611e3_sixBitAct
    apply Finset.sum_congr rfl
    intro i _
    have hlt : (x >>> ((Equiv.symm σ i : Fin 6) : Nat)) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    by_cases h : (x >>> ((Equiv.symm σ i : Fin 6) : Nat)) % 2 = 1
    · have hc : c i = true := by simp [c, h]
      simp [hc, Nat.and_one_is_mod, h]
    · have h0 : (x >>> ((Equiv.symm σ i : Fin 6) : Nat)) % 2 = 0 := by omega
      have hc : c i = false := by simp [c, h, h0]
      simp [hc, Nat.and_one_is_mod, h0]
  rw [hsum, s1611e3_bitSum_testBit]
  simp [c, Nat.and_one_is_mod, beq_iff_eq]

private theorem s1611e3_sixBitAct_lt (σ : Perm (Fin 6)) (x : Nat) :
    s1611e3_sixBitAct σ x < 64 := by
  have hb : ∀ i : Fin 6, ((x >>> ((σ⁻¹ i : Fin 6) : Nat)) &&& 1) ≤ 1 := fun _ =>
    Nat.and_le_right
  calc s1611e3_sixBitAct σ x
      = ∑ i : Fin 6, ((x >>> ((σ⁻¹ i : Fin 6) : Nat)) &&& 1) * 2 ^ (i : Nat) := rfl
    _ ≤ ∑ i : Fin 6, 1 * 2 ^ (i : Nat) := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul_right _ (hb i)
    _ = 63 := by decide
    _ < 64 := by norm_num

private theorem s1611e3_and63_shift (n k : Nat) (hk : k < 6) :
    ((n &&& 63) >>> k) &&& 1 = (n >>> k) &&& 1 := by
  rw [show (1 : Nat) = 2 ^ 0 by norm_num, Nat.and_two_pow, Nat.and_two_pow]
  simp only [Nat.pow_zero, Nat.mul_one]
  congr 1
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_land,
    show (63 : Nat) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  simp [hk]

private theorem s1611e3_sixBitAct_mod (σ : Perm (Fin 6)) (n : Nat) :
    s1611e3_sixBitAct σ n = s1611e3_sixBitAct σ (n &&& 63) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · have h1 := s1611e3_sixBitAct_testBit σ n ⟨i, hi⟩
    have h2 := s1611e3_sixBitAct_testBit σ (n &&& 63) ⟨i, hi⟩
    rw [h1, h2]
    have hk : ((σ⁻¹ (⟨i, hi⟩ : Fin 6) : Fin 6) : Nat) < 6 :=
      (σ⁻¹ (⟨i, hi⟩ : Fin 6)).isLt
    rw [s1611e3_and63_shift n ((σ⁻¹ (⟨i, hi⟩ : Fin 6) : Fin 6) : Nat) hk]
  · have hle : (64 : Nat) ≤ 2 ^ i := by
      rw [show (64 : Nat) = 2 ^ 6 by norm_num]
      exact Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    have h1 : s1611e3_sixBitAct σ n < 2 ^ i := by
      exact lt_of_lt_of_le (s1611e3_sixBitAct_lt σ n) hle
    have h2 : s1611e3_sixBitAct σ (n &&& 63) < 2 ^ i := by
      exact lt_of_lt_of_le (s1611e3_sixBitAct_lt σ (n &&& 63)) hle
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

theorem sixCodeAct_eq_tab (c : s1611e3_SixCode) (m : Nat) :
    s1611e3_sixCodeAct c m = sixTabAct (sixCodeTab c) m := by
  obtain ⟨σ, τ, ε⟩ := c
  have hx : m &&& 63 < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hy : (m >>> 6) &&& 63 < 64 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hb0 : ∀ i, i < 64 → sixTabImg (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 0 i < 4096 :=
    fun i _ =>
      s1611e3_sixTabImg_lt (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 0 i
        (fun k _ => by
          rw [s1611e3_sixTabDigit_sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode) (0 + k) (by omega)]
          exact s1611e3_sixDest_lt _ (0 + k))
  have hb6 : ∀ i, i < 64 → sixTabImg (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 6 i < 4096 :=
    fun i _ =>
      s1611e3_sixTabImg_lt (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 6 i
        (fun k _ => by
          rw [s1611e3_sixTabDigit_sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode) (6 + k) (by omega)]
          exact s1611e3_sixDest_lt _ (6 + k))
  have himg0 := s1611e3_sixTabImg_zero_eq (⟨σ, τ, ε⟩ : s1611e3_SixCode) (m &&& 63) hx
  have himg6 := s1611e3_sixTabImg_six_eq (⟨σ, τ, ε⟩ : s1611e3_SixCode) ((m >>> 6) &&& 63) hy
  unfold sixTabAct s1611e3_sixCodeAct
  rw [show sixTabLo (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) =
        s1611e3_pack (fun h => sixTabImg (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 0 h) 64
        from rfl,
      show sixTabHi (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) =
        s1611e3_pack (fun h => sixTabImg (sixCodeTab (⟨σ, τ, ε⟩ : s1611e3_SixCode)) 6 h) 64
        from rfl]
  rw [s1611e3_pack_extract _ hb0 (m &&& 63) hx,
      s1611e3_pack_extract _ hb6 ((m >>> 6) &&& 63) hy, himg0, himg6]
  rw [s1611e3_sixBitAct_mod τ (m >>> 6)]
  cases ε
  · simp only [Bool.false_eq_true, if_false, reduceIte]
    have hltA : s1611e3_sixBitAct σ (m &&& 63) < 2 ^ 6 := by
      have := s1611e3_sixBitAct_lt σ (m &&& 63)
      norm_num at this ⊢
      exact this
    have hshift : s1611e3_sixBitAct τ ((m >>> 6) &&& 63) <<< 6 =
        2 ^ 6 * s1611e3_sixBitAct τ ((m >>> 6) &&& 63) := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [show (64 : Nat) = 2 ^ 6 by norm_num, hshift, Nat.add_comm, Nat.or_comm]
    exact Nat.two_pow_add_eq_or_of_lt hltA (s1611e3_sixBitAct τ ((m >>> 6) &&& 63))
  · simp only [if_true, reduceIte]
    have hltB : s1611e3_sixBitAct τ ((m >>> 6) &&& 63) < 2 ^ 6 := by
      have := s1611e3_sixBitAct_lt τ ((m >>> 6) &&& 63)
      norm_num at this ⊢
      exact this
    have hshift : s1611e3_sixBitAct σ (m &&& 63) <<< 6 =
        2 ^ 6 * s1611e3_sixBitAct σ (m &&& 63) := by
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [show (64 : Nat) = 2 ^ 6 by norm_num, hshift, Nat.add_comm]
    exact Nat.two_pow_add_eq_or_of_lt hltB (s1611e3_sixBitAct σ (m &&& 63))

theorem sixCodeTab_mul (c d : s1611e3_SixCode) :
    sixCodeTab (s1611e3_sixCodeMul c d) = sixTabComp (sixCodeTab c) (sixCodeTab d) := by
  apply s1611e3_tab_ext
  · exact s1611e3_sixCodeTab_lt _
  · rw [s1611e3_tabComp_eq_orShift]
    exact s1611e3_orShift_lt
      (fun j => sixTabDigit (sixCodeTab c) (sixTabDigit (sixCodeTab d) j)) 12
      (fun i _ => s1611e3_sixTabDigit_lt _ _)
  · intro j hj
    rw [s1611e3_sixTabDigit_sixCodeTab _ _ hj,
      s1611e3_sixTabDigit_tabComp (sixCodeTab c) (sixCodeTab d) j hj,
      s1611e3_sixTabDigit_sixCodeTab d j hj,
      s1611e3_sixTabDigit_sixCodeTab c _ (by have := s1611e3_sixDest_lt d j; omega),
      s1611e3_sixDest_mul c d hj]

theorem sixCodeTab_injective : Function.Injective sixCodeTab := by
  intro c d h
  have hdest : ∀ j, j < 12 → s1611e3_sixDest c j = s1611e3_sixDest d j := by
    intro j hj
    rw [← s1611e3_sixTabDigit_sixCodeTab c j hj, h, s1611e3_sixTabDigit_sixCodeTab d j hj]
  obtain ⟨σ1, τ1, ε1⟩ := c
  obtain ⟨σ2, τ2, ε2⟩ := d
  have heps : ε1 = ε2 :=
    s1611e3_eps_eq_of_sixDest ⟨σ1, τ1, ε1⟩ ⟨σ2, τ2, ε2⟩ (hdest 0 (by norm_num))
  have hsigma : σ1 = σ2 := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rw [s1611e3_sixDest_sigma (⟨σ1, τ1, ε1⟩ : s1611e3_SixCode) i,
      s1611e3_sixDest_sigma (⟨σ2, τ2, ε2⟩ : s1611e3_SixCode) i]
    simp only
    rw [hdest i.val (by omega), heps]
  have htau : τ1 = τ2 := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    rw [s1611e3_sixDest_tau (⟨σ1, τ1, ε1⟩ : s1611e3_SixCode) i,
      s1611e3_sixDest_tau (⟨σ2, τ2, ε2⟩ : s1611e3_SixCode) i]
    simp only
    rw [hdest (i.val + 6) (by omega), heps]
  cases hsigma
  cases htau
  cases heps
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
