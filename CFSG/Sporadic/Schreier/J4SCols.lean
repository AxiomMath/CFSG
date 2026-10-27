module

public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

abbrev app11 (C : Array ℕ) (a : ℕ) : ℕ := vecMulN 11 C a

@[expose] def colsMatrix (C : Array ℕ) : Matrix (Fin 11) (Fin 11) (ZMod 2) := (rowsMatrix 11 C)ᵀ

@[expose] def comp11 (C D : Array ℕ) : Array ℕ := mulRows 11 D C

theorem colsMatrix_apply (C : Array ℕ) (i j : Fin 11) :
    colsMatrix C i j = toVecD 11 (C[j.val]?.getD 0) i := rfl

theorem colsMatrix_comp11 (C D : Array ℕ) :
    colsMatrix (comp11 C D) = colsMatrix C * colsMatrix D := by
  rw [colsMatrix, comp11, rowsMatrix_mulRows, Matrix.transpose_mul]
  rfl

theorem colsMatrix_idRows : colsMatrix (idRows 11) = 1 := by
  rw [colsMatrix, rowsMatrix_idRows, Matrix.transpose_one]

theorem colsMatrix_mulVec (C : Array ℕ) (a : ℕ) :
    colsMatrix C *ᵥ toVecD 11 a = toVecD 11 (app11 C a) := by
  rw [colsMatrix, Matrix.mulVec_transpose, toVecD_vecMulN]

@[expose] noncomputable def glOf (C D : Array ℕ) (h : comp11 C D = idRows 11) :
    GL (Fin 11) (ZMod 2) where
  val := colsMatrix C
  inv := colsMatrix D
  val_inv := by rw [← colsMatrix_comp11, h, colsMatrix_idRows]
  inv_val := by
    have h1 : colsMatrix C * colsMatrix D = 1 := by rw [← colsMatrix_comp11, h, colsMatrix_idRows]
    rw [← Matrix.inv_eq_right_inv h1]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse h1)

theorem glOf_val (C D : Array ℕ) (h : comp11 C D = idRows 11) :
    ((glOf C D h : GL (Fin 11) (ZMod 2)) : Matrix (Fin 11) (Fin 11) (ZMod 2)) = colsMatrix C :=
  rfl

theorem glOf_inv_val (C D : Array ℕ) (h : comp11 C D = idRows 11) :
    (((glOf C D h)⁻¹ : GL (Fin 11) (ZMod 2)) : Matrix (Fin 11) (Fin 11) (ZMod 2)) =
      colsMatrix D :=
  rfl

theorem vecMulN_lt {d : ℕ} {R : Array ℕ} (hR : ∀ j < d, R[j]?.getD 0 < 2 ^ d) (v : ℕ) :
    vecMulN d R v < 2 ^ d := by
  unfold vecMulN
  suffices h : ∀ (l : List ℕ) (acc : ℕ), (∀ j ∈ l, j < d) → acc < 2 ^ d →
      l.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc < 2 ^ d by
    exact h _ 0 (fun j hj => List.mem_range.1 hj) (Nat.two_pow_pos d)
  intro l
  induction l with
  | nil => intro acc _ h; exact h
  | cons j l ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    refine ih _ (fun k hk => hl k (List.mem_cons_of_mem _ hk)) ?_
    split_ifs
    · exact Nat.xor_lt_two_pow hacc (hR j (hl j List.mem_cons_self))
    · exact hacc

theorem toVecD_two_pow {j : ℕ} (hj : j < 11) :
    toVecD 11 (2 ^ j) = Pi.single (⟨j, hj⟩ : Fin 11) 1 := by
  funext k
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases hk : k = ⟨j, hj⟩
  · subst hk; simp
  · have : j ≠ k.val := fun e => hk (Fin.ext e.symm)
    simp [hk, this]

theorem app11_two_pow {C : Array ℕ} (hC : ∀ j < 11, C[j]?.getD 0 < 2 ^ 11) {j : ℕ}
    (hj : j < 11) : app11 C (2 ^ j) = C[j]?.getD 0 := by
  refine toVecD_injective (vecMulN_lt hC _) (hC j hj) ?_
  rw [app11, toVecD_vecMulN, toVecD_two_pow hj, Matrix.single_one_vecMul]
  funext k
  rw [Matrix.row_apply, rowsMatrix_apply]

end CFSG.Sporadic.J4Schreier
