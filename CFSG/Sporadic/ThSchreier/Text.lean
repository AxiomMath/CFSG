module

public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def hexDigit (c : Char) : ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10 else 0

@[expose] def hexNat (s : String) : ℕ :=
  let cs := s.toList
  let cs := if cs.take 2 = ['0', 'x'] then cs.drop 2 else cs
  cs.foldl (fun acc c => 16 * acc + hexDigit c) 0

@[expose] def wordsOf (s : String) : List String :=
  ((s.splitOn "\n").flatMap fun l => l.splitOn " ").filter fun w => !w.isEmpty

@[expose] def natsOf (s : String) : List ℕ := (wordsOf s).map String.toNat!

@[expose] def hexsOf (s : String) : List ℕ := (wordsOf s).map hexNat

@[expose] def rowOfNat (n : ℕ) : Fin 248 → ZMod 2 := fun j => if n.testBit j.val then 1 else 0

@[expose] def v4OfNat (n : ℕ) : V4 :=
  ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩

theorem v4OfNat_toNat (n : ℕ) : (v4OfNat n).toNat = n % 2 ^ 256 := by
  simp only [V4.toNat, v4OfNat, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  have h1 : n % 2 ^ 128 = n % 2 ^ 64 + 2 ^ 64 * (n / 2 ^ 64 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
  have h2 : n % 2 ^ 192 = n % 2 ^ 128 + 2 ^ 128 * (n / 2 ^ 128 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 192 = 2 ^ 128 * 2 ^ 64 by norm_num, Nat.mod_mul]
  have h3 : n % 2 ^ 256 = n % 2 ^ 192 + 2 ^ 192 * (n / 2 ^ 192 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 256 = 2 ^ 192 * 2 ^ 64 by norm_num, Nat.mod_mul]
  rw [h3, h2, h1]

theorem v4OfNat_testBit (n : ℕ) {j : ℕ} (hj : j < 256) : (v4OfNat n).testBit j = n.testBit j := by
  rw [← V4.testBit_toNat _ hj, v4OfNat_toNat, Nat.testBit_mod_two_pow]
  simp [hj]

theorem toVec_v4OfNat (n : ℕ) : (v4OfNat n).toVec = rowOfNat n := by
  funext j
  rw [V4.toVec_apply, v4OfNat_testBit n (by omega), rowOfNat]

theorem v4OfNat_wf {n : ℕ} (hn : n < 2 ^ 248) : (v4OfNat n).wf = true := by
  rw [V4.wf_iff_toNat_lt, v4OfNat_toNat, Nat.mod_eq_of_lt (lt_trans hn (by norm_num))]
  exact hn

theorem v4OfNat_toNat_of_lt {n : ℕ} (hn : n < 2 ^ 248) : (v4OfNat n).toNat = n := by
  rw [v4OfNat_toNat, Nat.mod_eq_of_lt (lt_trans hn (by norm_num))]

theorem toVec_eq_rowOfNat (a : V4) : a.toVec = rowOfNat a.toNat := by
  funext j
  rw [V4.toVec_apply, rowOfNat, V4.testBit_toNat _ (by omega)]

theorem rowOfNat_injective {n m : ℕ} (hn : n < 2 ^ 248) (hm : m < 2 ^ 248)
    (h : rowOfNat n = rowOfNat m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 248
  · have := congrFun h ⟨j, hj⟩
    simp only [rowOfNat] at this
    cases hn' : n.testBit j <;> cases hm' : m.testBit j <;> simp_all
  · have h248 : (2 : ℕ) ^ 248 ≤ 2 ^ j := Nat.pow_le_pow_right two_pos (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn h248),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm h248)]

theorem rowOfNat_zero : rowOfNat 0 = 0 := by
  funext j
  simp [rowOfNat]

end CFSG.Sporadic.ThSchreier
