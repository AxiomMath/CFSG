module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.RepresentationTheory.SL2NatSum

private lemma bit_add_bit_mod_two (a b : Bool) (i k : ℕ) :
    (Nat.bit a i + Nat.bit b k) % 2 = (a ^^ b).toNat := by
  cases a <;> cases b <;> simp [Nat.bit] <;> omega

private lemma bit_add_bit_div_two (a b : Bool) (i k : ℕ) :
    (Nat.bit a i + Nat.bit b k) / 2 = i + k + (a && b).toNat := by
  cases a <;> cases b <;> simp [Nat.bit] <;> omega

theorem add_eq_or_of_and_eq_zero {i k : ℕ} (h : i &&& k = 0) : i + k = i ||| k := by
  revert k
  induction i using Nat.binaryRec with
  | zero => intro k _; simp
  | bit a i ih =>
    intro k h
    cases k using Nat.bitCasesOn with
    | bit b k =>
      have h' : Nat.bit (a && b) (i &&& k) = 0 := by
        simpa only [Nat.land_bit] using h
      cases a <;> cases b
      · have hk : i &&& k = 0 := by simpa using h'
        rw [← Nat.bit_add, Nat.lor_bit, ih hk]
        rfl
      · have hk : i &&& k = 0 := by simpa using h'
        rw [← Nat.bit_add, Nat.lor_bit, ih hk]
        rfl
      · have hk : i &&& k = 0 := by simpa using h'
        rw [← Nat.bit_add', Nat.lor_bit, ih hk]
        rfl
      · simp at h'

private lemma odd_iff_of_modEq_two {a b : ℕ} (h : a ≡ b [MOD 2]) : Odd a ↔ Odd b := by
  simp only [Nat.odd_iff, Nat.ModEq] at h ⊢
  rw [h]

private lemma not_odd_of_modEq_zero {a : ℕ} (h : a ≡ 0 [MOD 2]) : ¬ Odd a := by
  rw [Nat.not_odd_iff]
  simpa [Nat.ModEq] using h

theorem odd_choose_add_iff (i k : ℕ) : Odd ((i + k).choose i) ↔ i &&& k = 0 := by
  revert k
  induction i using Nat.binaryRec with
  | zero => intro k; simp
  | bit a i ih =>
    intro k
    cases k using Nat.bitCasesOn with
    | bit b k =>
      cases a <;> cases b
      · have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := Nat.bit false i + Nat.bit false k) (k := Nat.bit false i) (p := 2)
        rw [bit_add_bit_mod_two, bit_add_bit_div_two, Nat.bit_mod_two,
          Nat.bit_div_two] at hL
        rw [Nat.land_bit, Nat.bit_eq_zero_iff]
        simp only [Nat.bit_false_apply, Bool.toNat_false, Bool.and_self, Bool.xor_self,
          Nat.choose_zero_right, Nat.choose_self, Nat.add_zero, mul_one, one_mul,
          Bool.false_eq_true, and_true] at hL ⊢
        exact (odd_iff_of_modEq_two hL).trans (ih k)
      · have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := Nat.bit false i + Nat.bit true k) (k := Nat.bit false i) (p := 2)
        rw [bit_add_bit_mod_two, bit_add_bit_div_two, Nat.bit_mod_two,
          Nat.bit_div_two] at hL
        rw [Nat.land_bit, Nat.bit_eq_zero_iff]
        simp only [Nat.bit_false_apply, Nat.bit_true_apply, Bool.toNat_false, Bool.toNat_true,
          Bool.false_and, Bool.and_false, Bool.xor_false, Nat.choose_zero_right,
          Nat.choose_succ_self, Nat.add_zero, mul_one, one_mul, Bool.false_eq_true, and_true]
          at hL ⊢
        exact (odd_iff_of_modEq_two hL).trans (ih k)
      · have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := Nat.bit true i + Nat.bit false k) (k := Nat.bit true i) (p := 2)
        rw [bit_add_bit_mod_two, bit_add_bit_div_two, Nat.bit_mod_two,
          Nat.bit_div_two] at hL
        rw [Nat.land_bit, Nat.bit_eq_zero_iff]
        simp only [Nat.bit_false_apply, Nat.bit_true_apply, Bool.toNat_false, Bool.toNat_true,
          Bool.false_and, Bool.and_false, Bool.xor_false, Nat.choose_zero_right,
          Nat.choose_self, Nat.add_zero, mul_one, one_mul, Bool.false_eq_true, and_true]
          at hL ⊢
        exact (odd_iff_of_modEq_two hL).trans (ih k)
      · have hL := Choose.choose_modEq_choose_mod_mul_choose_div_nat
          (n := Nat.bit true i + Nat.bit true k) (k := Nat.bit true i) (p := 2)
        rw [bit_add_bit_mod_two, bit_add_bit_div_two, Nat.bit_mod_two,
          Nat.bit_div_two] at hL
        rw [Nat.land_bit, Nat.bit_eq_zero_iff]
        simp only [Nat.bit_false_apply, Nat.bit_true_apply, Bool.toNat_true, Bool.and_self,
          Bool.xor_self, Nat.choose_zero_succ, Nat.add_zero, zero_mul, mul_one, one_mul,
          Bool.true_eq_false, false_and, not_false_eq_true, iff_false] at hL ⊢
        have hL' : (2 * i + 1 + (2 * k + 1)).choose (2 * i + 1) ≡ 0 [MOD 2] := by
          simpa using hL
        simpa [and_false] using not_odd_of_modEq_zero hL'

end CFSG.RepresentationTheory.SL2NatSum
