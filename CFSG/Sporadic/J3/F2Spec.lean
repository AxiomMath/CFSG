module

public import Certificates.Data.CFSGNative.J3.Basic
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.J3

open Native Finset
open scoped Matrix

@[expose] def toVecD (d : ℕ) (x : ℕ) : Fin d → ZMod 2 := fun j => if x.testBit j.val then 1 else 0

theorem toVecD_apply (d x : ℕ) (j : Fin d) : toVecD d x j = if x.testBit j.val then 1 else 0 :=
  rfl

theorem toVecD_xor (d x y : ℕ) : toVecD d (x ^^^ y) = toVecD d x + toVecD d y := by
  funext j
  simp only [toVecD, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> decide

theorem toVecD_zero (d : ℕ) : toVecD d 0 = 0 := by
  funext j; simp [toVecD]

theorem toVecD_injective {d x y : ℕ} (hx : x < 2 ^ d) (hy : y < 2 ^ d)
    (h : toVecD d x = toVecD d y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    simp only [toVecD] at this
    cases hxj : x.testBit j <;> cases hyj : y.testBit j <;> simp_all
  · have hle : 2 ^ d ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hle)]

theorem foldl_xor_toVecD (d : ℕ) (P : ℕ → Prop) [DecidablePred P] (g : ℕ → ℕ) (m init : ℕ) :
    toVecD d ((List.range m).foldl (fun acc i => if P i then acc ^^^ g i else acc) init) =
      toVecD d init + ∑ i ∈ range m, if P i then toVecD d (g i) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
      ← add_assoc, ← ih]
    split_ifs <;> simp [toVecD_xor]

theorem foldl_or_testBit (f : ℕ → Bool) (m i : ℕ) :
    ((List.range m).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0).testBit i =
      (decide (i < m) && f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with hf
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1, Ne.symm him]
    · rw [ih]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1]

theorem ofBits_testBit (d : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (ofBits d f).testBit i = (decide (i < d) && f i) :=
  foldl_or_testBit f d i

theorem toVecD_ofBits (d : ℕ) (f : ℕ → Bool) (j : Fin d) :
    toVecD d (ofBits d f) j = if f j.val then 1 else 0 := by
  rw [toVecD_apply, ofBits_testBit]
  simp [j.isLt]

@[expose] def rowsMatrix (d : ℕ) (R : Array ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  Matrix.of fun i j => toVecD d (R[i.val]?.getD 0) j

theorem rowsMatrix_apply (d : ℕ) (R : Array ℕ) (i j : Fin d) :
    rowsMatrix d R i j = toVecD d (R[i.val]?.getD 0) j := rfl

theorem toVecD_vecMulN (d : ℕ) (R : Array ℕ) (v : ℕ) :
    toVecD d (vecMulN d R v) = toVecD d v ᵥ* rowsMatrix d R := by
  unfold vecMulN
  rw [foldl_xor_toVecD, toVecD_zero, zero_add]
  funext k
  simp only [Finset.sum_apply, Matrix.vecMul, dotProduct, rowsMatrix_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i =>
    (if v.testBit i = true then toVecD d (R[i]?.getD 0) else 0) k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply]
  split_ifs <;> simp

theorem rowsMatrix_transposeRows (d : ℕ) (R : Array ℕ) :
    rowsMatrix d (transposeRows d R) = (rowsMatrix d R)ᵀ := by
  ext j i
  rw [Matrix.transpose_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold transposeRows
  simp only [Array.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_ofBits, toVecD_apply]

theorem rowsMatrix_mulVec (d : ℕ) (R : Array ℕ) (v : ℕ) :
    rowsMatrix d R *ᵥ toVecD d v = toVecD d (vecMulN d (transposeRows d R) v) := by
  rw [toVecD_vecMulN, rowsMatrix_transposeRows, Matrix.vecMul_transpose]

theorem rowsMatrix_mulRows (d : ℕ) (X Y : Array ℕ) :
    rowsMatrix d (mulRows d X Y) = rowsMatrix d X * rowsMatrix d Y := by
  ext i k
  rw [Matrix.mul_apply, rowsMatrix_apply]
  unfold mulRows
  rw [Array.getElem?_map]
  simp only [rowsMatrix_apply]
  cases X[i.val]? with
  | none => simp [toVecD_zero]
  | some x =>
    rw [Option.map_some, Option.getD_some, Option.getD_some, toVecD_vecMulN]
    rfl

theorem rowsMatrix_idRows (d : ℕ) : rowsMatrix d (idRows d) = 1 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.one_apply]
  unfold idRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_apply, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem rowsMatrix_powRows (d : ℕ) (M : Array ℕ) (e : ℕ) :
    rowsMatrix d (powRows d M e) = rowsMatrix d M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact rowsMatrix_idRows d
  | succ e ih => rw [powRows, rowsMatrix_mulRows, ih, pow_succ]

theorem wsChar_eq_asciiWhitespace :
    Th.Native.wsChar = CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  funext c; unfold Th.Native.wsChar; rfl

theorem decode_apply_eq_decodeEntries (d : ℕ) (s : String) (i j : Fin d) :
    CFSG.Blueprint.NativeSporadic.decode 2 d 1 s i j =
      (((Th.Native.decodeEntries s)[i.val * d + j.val]?.getD 0 : ℕ) : ZMod 2) := by
  unfold Th.Native.decodeEntries
  rw [wsChar_eq_asciiWhitespace]
  rfl

private theorem natCast_zmod_two (n : ℕ) :
    (n : ZMod 2) = if (n % 2 == 1) = true then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem rowsMatrix_rowsOfPayload (d : ℕ) (s : String) :
    rowsMatrix d (rowsOfPayload d s) = CFSG.Blueprint.NativeSporadic.decode 2 d 1 s := by
  ext i j
  rw [decode_apply_eq_decodeEntries, rowsMatrix_apply]
  unfold rowsOfPayload
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_ofBits, List.getElem?_toArray, natCast_zmod_two]

end CFSG.Sporadic.J3
