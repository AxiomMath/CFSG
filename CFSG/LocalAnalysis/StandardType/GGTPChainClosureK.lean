module

public import CFSG.LocalAnalysis.StandardType.GGTPChainK

public section

namespace CFSG.StandardType.GGTPK

open E6Dep

@[expose] def bitK (m i : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

@[expose] def orN (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.lor acc (f j)) n

@[expose] def rowK (m a : ℕ) : ℕ :=
  orN 36 (fun b => Bool.rec 0 (Nat.shiftLeft 1 (cjL a b)) (bitK m b))

@[expose] def stepK (m : ℕ) : ℕ :=
  Nat.lor m (orN 36 (fun a => Bool.rec 0 (rowK m a) (bitK m a)))

theorem bitK_eq (m i : ℕ) : bitK m i = m.testBit i := by
  have h : Nat.land (Nat.shiftRight m i) 1 = m / 2 ^ i % 2 := by
    change (m >>> i) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bitK
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h1 : m / 2 ^ i % 2 = 1
  · rw [h1]
    simp
  · rw [decide_eq_false h1]
    cases hb : Nat.beq (m / 2 ^ i % 2) 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h1

theorem bitK_lor (x y i : ℕ) : bitK (Nat.lor x y) i = (bitK x i || bitK y i) := by
  rw [bitK_eq, bitK_eq, bitK_eq]
  exact Nat.testBit_or x y i

theorem bitK_zero (i : ℕ) : bitK 0 i = false := by
  rw [bitK_eq]
  exact Nat.zero_testBit i

theorem bitK_shift1 {k i : ℕ} (h : bitK (Nat.shiftLeft 1 k) i = true) : i = k := by
  rw [bitK_eq] at h
  have e : Nat.shiftLeft 1 k = 2 ^ k := by
    change 1 <<< k = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e, Nat.testBit_two_pow] at h
  exact (of_decide_eq_true h).symm

theorem bitK_rec {c : Bool} {x i : ℕ} (h : bitK (Bool.rec (motive := fun _ => ℕ) 0 x c) i = true) :
    c = true ∧ bitK x i = true := by
  cases c
  · rw [bitK_zero] at h
    exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bitK_orN {n : ℕ} {f : ℕ → ℕ} {i : ℕ} (h : bitK (orN n f) i = true) :
    ∃ j < n, bitK (f j) i = true := by
  induction n with
  | zero =>
    have h' : bitK 0 i = true := h
    rw [bitK_zero] at h'
    exact absurd h' Bool.false_ne_true
  | succ n ih =>
    have h' : bitK (Nat.lor (orN n f) (f n)) i = true := h
    rw [bitK_lor, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · obtain ⟨j, hj, hf⟩ := ih h'
      exact ⟨j, Nat.lt_succ_of_lt hj, hf⟩
    · exact ⟨n, Nat.lt_succ_self n, h'⟩

theorem cjL_eq {a b : ℕ} (ha : a < 36) (hb : b < 36) : cjL a b = cjN a b := by
  rw [cjN_eq_cjK]
  unfold cjK
  have ha' : Nat.blt a 36 = true := Nat.ble_eq_true_of_le ha
  have hb' : Nat.blt b 36 = true := Nat.ble_eq_true_of_le hb
  rw [ha', hb']

theorem stepK_sub {J : Finset ℕ} (hJ : CjClosed J) {m : ℕ}
    (hm : ∀ i < 36, bitK m i = true → i ∈ J) : ∀ i < 36, bitK (stepK m) i = true → i ∈ J := by
  intro i hi h
  have h' : bitK (Nat.lor m (orN 36 (fun a => Bool.rec 0 (rowK m a) (bitK m a)))) i = true := h
  rw [bitK_lor, Bool.or_eq_true] at h'
  rcases h' with h' | h'
  · exact hm i hi h'
  · obtain ⟨a, ha, hr⟩ := bitK_orN h'
    obtain ⟨hma, hr⟩ := bitK_rec hr
    obtain ⟨b, hb, hs⟩ := bitK_orN hr
    obtain ⟨hmb, hs⟩ := bitK_rec hs
    rw [bitK_shift1 hs, cjL_eq ha hb]
    exact hJ a (hm a ha hma) b (hm b hb hmb)

theorem bitK_of_full {M i : ℕ} (h : Nat.land M 68719476735 = 68719476735) (hi : i < 36) :
    bitK M i = true := by
  rw [bitK_eq]
  have e : (68719476735 : ℕ) = 2 ^ 36 - 1 := rfl
  have hF : (2 ^ 36 - 1 : ℕ).testBit i = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hi
  have hh := congrArg (fun k => k.testBit i) h
  change (M &&& 68719476735).testBit i = (68719476735 : ℕ).testBit i at hh
  rw [e, Nat.testBit_and, hF, Bool.and_true] at hh
  exact hh

end CFSG.StandardType.GGTPK

end
