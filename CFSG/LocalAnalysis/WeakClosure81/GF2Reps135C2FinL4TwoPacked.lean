module

public import CFSG.LargeExtraspecial.SL4ModClassSpec
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoPivot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.LargeExtraspecial.SL4Mod

theorem getElem!_eq_getElem?_getD (a : Array ℕ) (i : ℕ) : a[i]! = a[i]?.getD 0 := by
  rw [getElem!_def]
  cases a[i]? <;> rfl

theorem refMat_eq_transpose_rowsMatrix (d : ℕ) (cols : Array ℕ) :
    refMat d cols = (rowsMatrix d cols)ᵀ := by
  ext m k
  rw [Matrix.transpose_apply, rowsMatrix_apply, toVecD_apply, refMat, Matrix.of_apply,
    getElem!_eq_getElem?_getD]

theorem refMat_mulVec (d : ℕ) (cols : Array ℕ) (x : ℕ) :
    refMat d cols *ᵥ toVecD d x = toVecD d (vecMulN d cols x) := by
  rw [toVecD_vecMulN, refMat_eq_transpose_rowsMatrix, Matrix.mulVec_transpose]

@[expose] def colMul (d : ℕ) (A B : Array ℕ) : Array ℕ := mulRows d B A

theorem refMat_colMul (d : ℕ) (A B : Array ℕ) :
    refMat d (colMul d A B) = refMat d A * refMat d B := by
  rw [colMul, refMat_eq_transpose_rowsMatrix, rowsMatrix_mulRows, Matrix.transpose_mul,
    refMat_eq_transpose_rowsMatrix, refMat_eq_transpose_rowsMatrix]

theorem refMat_idRows (d : ℕ) : refMat d (idRows d) = 1 := by
  rw [refMat_eq_transpose_rowsMatrix, rowsMatrix_idRows, Matrix.transpose_one]

@[expose] def colWord (d : ℕ) (g : ℕ → Array ℕ) (w : List ℕ) : Array ℕ :=
  w.foldr (fun s acc => colMul d (g s) acc) (idRows d)

theorem refMat_colWord (d : ℕ) (g : ℕ → Array ℕ) (w : List ℕ) :
    refMat d (colWord d g w) = (w.map fun s => refMat d (g s)).prod := by
  induction w with
  | nil => exact refMat_idRows d
  | cons s w ih =>
    rw [colWord, List.foldr_cons, refMat_colMul, ← colWord, ih, List.map_cons, List.prod_cons]

@[expose] def colSubOne (d : ℕ) (C : Array ℕ) : Array ℕ :=
  Array.ofFn (n := d) fun k => C[k.val]! ^^^ (1 <<< k.val)

theorem getElem!_colSubOne (d : ℕ) (C : Array ℕ) (k : Fin d) :
    (colSubOne d C)[k.val]! = C[k.val]! ^^^ (1 <<< k.val) := by
  rw [getElem!_eq_getElem?_getD, colSubOne]
  simp only [Array.getElem?_ofFn, k.isLt, ↓reduceDIte, Option.getD_some]

theorem refMat_colSubOne (d : ℕ) (C : Array ℕ) : refMat d (colSubOne d C) = refMat d C - 1 := by
  ext m k
  rw [refMat, Matrix.of_apply, getElem!_colSubOne, Matrix.sub_apply, refMat, Matrix.of_apply,
    Matrix.one_apply, Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : m = k
  · subst h
    cases (C[m.val]!).testBit m.val <;> simp <;> decide
  · have h' : k.val ≠ m.val := fun e => h (Fin.ext e.symm)
    simp only [h, h', decide_false, Bool.xor_false, if_false, sub_zero]

@[expose] def pivChk (d n : ℕ) (C xs ps : Array ℕ) : Bool :=
  (List.range n).all fun k =>
    decide (ps[k]! < d) && (vecMulN d C xs[k]!).testBit ps[k]! &&
      (List.range n).all fun j => decide (j ≤ k) || !((vecMulN d C xs[j]!).testBit ps[k]!)

theorem le_finrank_range_of_pivChk {d n : ℕ} {C xs ps : Array ℕ}
    (h : pivChk d n C xs ps = true) :
    n ≤ finrank (ZMod 2) (LinearMap.range (refMat d C).mulVecLin) := by
  have hk : ∀ k < n, ps[k]! < d ∧ (vecMulN d C xs[k]!).testBit ps[k]! = true ∧
      ∀ j < n, k < j → (vecMulN d C xs[j]!).testBit ps[k]! = false := by
    intro k hk
    have h1 := (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
    refine ⟨h1.1.1, h1.1.2, fun j hj hkj => ?_⟩
    have h2 := (List.all_eq_true.mp h1.2) j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h2
    · rcases h2 with h2 | h2
      · omega
      · exact Bool.not_eq_true _ ▸ (by simpa using h2)
  refine le_finrank_range_of_pivots (refMat d C) (fun k : Fin n => toVecD d xs[k.val]!)
    (fun k => ⟨ps[k.val]!, (hk k.val k.isLt).1⟩) (fun k => ?_) (fun k j hkj => ?_)
  · rw [refMat_mulVec, toVecD_apply]
    simp [(hk k.val k.isLt).2.1]
  · rw [refMat_mulVec, toVecD_apply]
    simp [(hk k.val k.isLt).2.2 j.val j.isLt hkj]

@[expose] def kerChk (d n : ℕ) (C ys ps : Array ℕ) : Bool :=
  (List.range n).all fun k =>
    decide (ps[k]! < d) && (vecMulN d C ys[k]! == 0) && ys[k]!.testBit ps[k]! &&
      (List.range n).all fun j => decide (j ≤ k) || !(ys[j]!.testBit ps[k]!)

theorem le_finrank_ker_of_kerChk {d n : ℕ} {C ys ps : Array ℕ}
    (h : kerChk d n C ys ps = true) :
    n ≤ finrank (ZMod 2) (LinearMap.ker (refMat d C).mulVecLin) := by
  have hk : ∀ k < n, ps[k]! < d ∧ vecMulN d C ys[k]! = 0 ∧ ys[k]!.testBit ps[k]! = true ∧
      ∀ j < n, k < j → ys[j]!.testBit ps[k]! = false := by
    intro k hk
    have h1 := (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h1
    refine ⟨h1.1.1.1, h1.1.1.2, h1.1.2, fun j hj hkj => ?_⟩
    have h2 := (List.all_eq_true.mp h1.2) j (List.mem_range.mpr hj)
    rw [Bool.or_eq_true, decide_eq_true_eq] at h2
    rcases h2 with h2 | h2
    · omega
    · simpa using h2
  refine le_finrank_ker_of_pivots (refMat d C) (fun k : Fin n => toVecD d ys[k.val]!)
    (fun k => ⟨ps[k.val]!, (hk k.val k.isLt).1⟩) (fun k => ?_) (fun k => ?_) (fun k j hkj => ?_)
  · rw [refMat_mulVec, (hk k.val k.isLt).2.1, toVecD_zero]
  · rw [toVecD_apply]
    simp [(hk k.val k.isLt).2.2.1]
  · rw [toVecD_apply]
    simp [(hk k.val k.isLt).2.2.2 j.val j.isLt hkj]

end CFSG.LocalAnalysis.WeakClosure81
