module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open Matrix

section Blocks

variable {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommRing R]

@[expose] def IsBlockDiag (X : Matrix (α ⊕ β) (α ⊕ β) R) : Prop :=
  X.toBlocks₁₂ = 0 ∧ X.toBlocks₂₁ = 0

theorem eq_fromBlocks_of_isBlockDiag {X : Matrix (α ⊕ β) (α ⊕ β) R} (h : IsBlockDiag X) :
    X = fromBlocks X.toBlocks₁₁ 0 0 X.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks X]
  rw [h.1, h.2]

theorem isBlockDiag_of_commute {X : Matrix (α ⊕ β) (α ⊕ β) R}
    (h : X * fromBlocks 0 0 0 1 = fromBlocks 0 0 0 1 * X) : IsBlockDiag X := by
  rw [← fromBlocks_toBlocks X, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, zero_add,
    add_zero] at h
  obtain ⟨-, h12, h21, -⟩ := fromBlocks_inj.mp h
  refine ⟨?_, ?_⟩ <;> first | exact h12 | exact h12.symm | exact h21 | exact h21.symm

theorem toBlocks₁₁_one : (1 : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₁₁ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem toBlocks₂₂_one : (1 : Matrix (α ⊕ β) (α ⊕ β) R).toBlocks₂₂ = 1 := by
  rw [← fromBlocks_one, toBlocks_fromBlocks₂₂]

theorem fromBlocks_diag_mul (A A' : Matrix α α R) (B B' : Matrix β β R) :
    fromBlocks A 0 0 B * fromBlocks A' 0 0 B' = fromBlocks (A * A') 0 0 (B * B') := by
  rw [fromBlocks_multiply]
  simp

theorem fromBlocks_diag_pow (A : Matrix α α R) (B : Matrix β β R) (k : ℕ) :
    fromBlocks A 0 0 B ^ k = fromBlocks (A ^ k) 0 0 (B ^ k) := by
  induction k with
  | zero => simp [fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, fromBlocks_diag_mul, ← pow_succ, ← pow_succ]

theorem fromBlocks_diag_transpose (A : Matrix α α R) (B : Matrix β β R) :
    (fromBlocks A 0 0 B)ᵀ = fromBlocks Aᵀ 0 0 Bᵀ := by
  rw [fromBlocks_transpose]
  simp

theorem IsBlockDiag.toBlocks₁₁_mul {X Y : Matrix (α ⊕ β) (α ⊕ β) R} (hX : IsBlockDiag X)
    (hY : IsBlockDiag Y) : (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ := by
  conv_lhs => rw [eq_fromBlocks_of_isBlockDiag hX, eq_fromBlocks_of_isBlockDiag hY,
    fromBlocks_diag_mul]
  rw [toBlocks_fromBlocks₁₁]

theorem IsBlockDiag.toBlocks₂₂_mul {X Y : Matrix (α ⊕ β) (α ⊕ β) R} (hX : IsBlockDiag X)
    (hY : IsBlockDiag Y) : (X * Y).toBlocks₂₂ = X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  conv_lhs => rw [eq_fromBlocks_of_isBlockDiag hX, eq_fromBlocks_of_isBlockDiag hY,
    fromBlocks_diag_mul]
  rw [toBlocks_fromBlocks₂₂]

end Blocks

section Reindex

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [CommRing R]

@[expose] def bl (e : ι ≃ κ) (X : Matrix ι ι R) : Matrix κ κ R := X.submatrix e.symm e.symm

theorem bl_mul (e : ι ≃ κ) (X Y : Matrix ι ι R) : bl e (X * Y) = bl e X * bl e Y := by
  simp only [bl]
  rw [submatrix_mul_equiv X Y e.symm e.symm e.symm]

theorem bl_one (e : ι ≃ κ) : bl e (1 : Matrix ι ι R) = 1 := submatrix_one_equiv e.symm

theorem bl_pow (e : ι ≃ κ) (X : Matrix ι ι R) (k : ℕ) : bl e (X ^ k) = bl e X ^ k := by
  induction k with
  | zero => simp [bl_one]
  | succ k ih => rw [pow_succ, bl_mul, ih, pow_succ]

theorem bl_transpose (e : ι ≃ κ) (X : Matrix ι ι R) : bl e Xᵀ = (bl e X)ᵀ := by
  simp only [bl, transpose_submatrix]

theorem bl_add (e : ι ≃ κ) (X Y : Matrix ι ι R) : bl e (X + Y) = bl e X + bl e Y := rfl

theorem submatrix_bl (e : ι ≃ κ) (X : Matrix ι ι R) : (bl e X).submatrix e e = X := by
  ext i j
  simp [bl]

theorem bl_injective (e : ι ≃ κ) : Function.Injective (bl (R := R) e) := by
  intro X Y h
  rw [← submatrix_bl e X, ← submatrix_bl e Y, h]

theorem bl_submatrix (e : ι ≃ κ) (A : Matrix κ κ R) : bl e (A.submatrix e e) = A := by
  ext i j
  simp [bl]

theorem bl_commute (e : ι ≃ κ) {X Y : Matrix ι ι R} (h : X * Y = Y * X) :
    bl e X * bl e Y = bl e Y * bl e X := by
  rw [← bl_mul, ← bl_mul, h]

end Reindex

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
