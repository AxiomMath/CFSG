module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace Matrix.GeneralLinearGroup

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {R : Type*}

@[expose] def blockDiagonal [Semiring R] (A : GL m R) (B : GL n R) : GL (m ⊕ n) R where
  val := Matrix.fromBlocks (A : Matrix m m R) 0 0 (B : Matrix n n R)
  inv := Matrix.fromBlocks ((A⁻¹ : GL m R) : Matrix m m R) 0 0
    ((B⁻¹ : GL n R) : Matrix n n R)
  val_inv := by
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.fromBlocks_one]
  inv_val := by
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.fromBlocks_one]

@[simp] theorem coe_blockDiagonal [Semiring R] (A : GL m R) (B : GL n R) :
    (blockDiagonal A B : Matrix (m ⊕ n) (m ⊕ n) R) =
      Matrix.fromBlocks (A : Matrix m m R) 0 0 (B : Matrix n n R) := rfl

@[simp] theorem blockDiagonal_inv [Semiring R] (A : GL m R) (B : GL n R) :
    (blockDiagonal A B)⁻¹ = blockDiagonal A⁻¹ B⁻¹ := by
  apply Units.ext
  rfl

theorem det_blockDiagonal [CommRing R] (A : GL m R) (B : GL n R) :
    (blockDiagonal A B : Matrix (m ⊕ n) (m ⊕ n) R).det =
      (A : Matrix m m R).det * (B : Matrix n n R).det := by
  rw [coe_blockDiagonal, Matrix.det_fromBlocks_zero₂₁]

section Reindex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

@[expose] def blockReindex [Semiring R] (β : ι → κ) (b : κ) :
    GL ι R ≃* GL ({i // β i = b} ⊕ {i // β i ≠ b}) R :=
  Units.mapEquiv (Matrix.reindexRingEquiv R (Equiv.sumCompl (fun i => β i = b)).symm).toMulEquiv

theorem coe_blockReindex [Semiring R] (β : ι → κ) (b : κ) (A : GL ι R) :
    (blockReindex β b A : Matrix ({i // β i = b} ⊕ {i // β i ≠ b})
      ({i // β i = b} ⊕ {i // β i ≠ b}) R) =
    (Matrix.reindex (Equiv.sumCompl (fun i => β i = b)).symm
      (Equiv.sumCompl (fun i => β i = b)).symm) (A : Matrix ι ι R) := by
  rw [blockReindex, Units.coe_mapEquiv]
  change (Matrix.reindexRingEquiv R (Equiv.sumCompl (fun i => β i = b)).symm)
    (A : Matrix ι ι R) = _
  rw [Matrix.coe_reindexRingEquiv]

theorem coe_blockReindex_of_isBlockDiag [Semiring R] (β : ι → κ) (b : κ)
    (A : GL ι R) (hA : ∀ i j : ι, β i ≠ β j → (A : Matrix ι ι R) i j = 0) :
    (blockReindex β b A : Matrix ({i // β i = b} ⊕ {i // β i ≠ b})
      ({i // β i = b} ⊕ {i // β i ≠ b}) R) =
      Matrix.fromBlocks ((A : Matrix ι ι R).toSquareBlock β b) 0 0
        ((A : Matrix ι ι R).submatrix
          (fun i : {i // β i ≠ b} => (i : ι)) (fun i : {i // β i ≠ b} => (i : ι))) := by
  rw [coe_blockReindex]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def]
  · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
      hA i j (fun h => j.2 (h.symm.trans i.2))
  · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using
      hA i j (fun h => i.2 (h.trans j.2))
  · simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem det_blockReindex [CommRing R] (β : ι → κ) (b : κ) (A : GL ι R) :
    (blockReindex β b A : Matrix ({i // β i = b} ⊕ {i // β i ≠ b})
      ({i // β i = b} ⊕ {i // β i ≠ b}) R).det = (A : Matrix ι ι R).det := by
  rw [coe_blockReindex, Matrix.det_reindex_self]

end Reindex

end Matrix.GeneralLinearGroup
