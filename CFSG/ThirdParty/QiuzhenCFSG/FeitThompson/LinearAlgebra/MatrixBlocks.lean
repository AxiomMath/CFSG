module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace

namespace CFSG
end CFSG
open CFSG

/-!
# Matrix block and trace helpers

This file collects elementary finite matrix identities used by the Wielandt
fixed-point infrastructure.
-/

noncomputable section

/-- The trace of a `2 x 2` block matrix is the sum of the traces of its
diagonal blocks. -/
public theorem CFSG.matrix_trace_fromBlocks
    {R l r : Type*} [AddCommMonoid R] [Fintype l] [Fintype r]
    (A : Matrix l l R) (B : Matrix l r R)
    (C : Matrix r l R) (D : Matrix r r R) :
    Matrix.trace (Matrix.fromBlocks A B C D) =
      Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Matrix trace is invariant under reindexing rows and columns by the same
equivalence. -/
public theorem CFSG.matrix_trace_reindex
    {R α β : Type*} [AddCommMonoid R] [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix α α R) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  rw [Matrix.trace, Matrix.trace]
  exact (e.symm.sum_comp (fun i => M i i)).trans (by rfl)


/-- Block trace reduction for a finite sum of conjugated block matrices. -/
public theorem CFSG.matrix_trace_sum_of_block_trace_data
    {R α l r : Type*} [CommSemiring R]
    [Fintype α] [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r]
    (M : α → Matrix (l ⊕ r) (l ⊕ r) R)
    (P Q : Matrix (l ⊕ r) (l ⊕ r) R)
    (hPQ : P * Q = 1)
    (h22 : ∀ a, (Q * M a * P).toBlocks₂₂ = 1)
    (h11 : (∑ a, (Q * M a * P).toBlocks₁₁) = 0) :
    Matrix.trace (∑ a, M a) =
      (Fintype.card r : R) * (Fintype.card α : R) := by
  classical
  have hconj :
      Matrix.trace (∑ a, Q * M a * P) = Matrix.trace (∑ a, M a) := by
    rw [Matrix.trace_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    calc
      Matrix.trace (Q * M a * P) = Matrix.trace (P * (Q * M a)) := by
        rw [Matrix.trace_mul_comm]
      _ = Matrix.trace ((P * Q) * M a) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace (M a) := by
        simp [hPQ]
  have hblock :
      Matrix.trace (∑ a, Q * M a * P) =
        Matrix.trace (∑ a, (Q * M a * P).toBlocks₁₁) +
          Matrix.trace (∑ a, (Q * M a * P).toBlocks₂₂) := by
    calc
      Matrix.trace (∑ a, Q * M a * P) =
          ∑ a, Matrix.trace (Q * M a * P) := by
        rw [Matrix.trace_sum]
      _ = ∑ a, (Matrix.trace (Q * M a * P).toBlocks₁₁ +
            Matrix.trace (Q * M a * P).toBlocks₂₂) := by
        apply Finset.sum_congr rfl
        intro a _ha
        calc
          Matrix.trace (Q * M a * P) =
              Matrix.trace (Matrix.fromBlocks (Q * M a * P).toBlocks₁₁
                (Q * M a * P).toBlocks₁₂ (Q * M a * P).toBlocks₂₁
                (Q * M a * P).toBlocks₂₂) := by
            rw [Matrix.fromBlocks_toBlocks]
          _ = Matrix.trace (Q * M a * P).toBlocks₁₁ +
              Matrix.trace (Q * M a * P).toBlocks₂₂ := by
            rw [matrix_trace_fromBlocks]
      _ = (∑ a, Matrix.trace (Q * M a * P).toBlocks₁₁) +
            (∑ a, Matrix.trace (Q * M a * P).toBlocks₂₂) := by
        rw [Finset.sum_add_distrib]
      _ = Matrix.trace (∑ a, (Q * M a * P).toBlocks₁₁) +
          Matrix.trace (∑ a, (Q * M a * P).toBlocks₂₂) := by
        rw [Matrix.trace_sum, Matrix.trace_sum]
  have htop : Matrix.trace (∑ a, (Q * M a * P).toBlocks₁₁) = 0 := by
    rw [h11]
    simp
  have hbot :
      Matrix.trace (∑ a, (Q * M a * P).toBlocks₂₂) =
        (Fintype.card r : R) * (Fintype.card α : R) := by
    rw [Matrix.trace_sum]
    simp [h22]
    ring
  rw [← hconj, hblock, htop, hbot, zero_add]

/-- Per-subgroup block data after a reindexing of the ambient matrix gives the
subgroup trace formula used by the matrix-trace model. -/
public theorem CFSG.trace_model_subgroup_sum_of_reindexed_block_data
    {G κ l r : Type*} [Group G] [Fintype κ] [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r]
    (A : Subgroup G) [Fintype A] (q : ℕ)
    (M : G → Matrix κ κ (ZMod q))
    (e : κ ≃ l ⊕ r)
    (P Q : Matrix (l ⊕ r) (l ⊕ r) (ZMod q))
    (hPQ : P * Q = 1)
    (h22 : ∀ a : A, (Q * Matrix.reindex e e (M (a : G)) * P).toBlocks₂₂ = 1)
    (h11 : (∑ a : A, (Q * Matrix.reindex e e (M (a : G)) * P).toBlocks₁₁) = 0) :
    Matrix.trace (∑ a : A, M (a : G)) =
      (Fintype.card r : ZMod q) * (Nat.card A : ZMod q) := by
  classical
  have htrace_reindex_sum :
      Matrix.trace (∑ a : A, M (a : G)) =
        Matrix.trace (∑ a : A, Matrix.reindex e e (M (a : G))) := by
    rw [Matrix.trace_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [matrix_trace_reindex]
  rw [htrace_reindex_sum]
  simpa [Nat.card_eq_fintype_card] using
    matrix_trace_sum_of_block_trace_data
      (M := fun a : A => Matrix.reindex e e (M (a : G)))
      (P := P) (Q := Q) hPQ h22 h11

/-- Assemble a square matrix from two block columns. -/
public def CFSG.matrixOfBlockColumns {R l r : Type*}
    (left : Matrix (l ⊕ r) l R) (right : Matrix (l ⊕ r) r R) :
    Matrix (l ⊕ r) (l ⊕ r) R :=
  fun i => Sum.elim (left i) (right i)

/-- Assemble a square matrix from two block rows. -/
public def CFSG.matrixOfBlockRows {R l r : Type*}
    (top : Matrix l (l ⊕ r) R) (bottom : Matrix r (l ⊕ r) R) :
    Matrix (l ⊕ r) (l ⊕ r) R :=
  Sum.elim top bottom

/-- The canonical inclusion of the left block into a direct-sum indexed matrix. -/
public def CFSG.identityBlockLeftColumn {R l r : Type*} [Zero R] [One R]
    [DecidableEq (l ⊕ r)] : Matrix (l ⊕ r) l R :=
  (1 : Matrix (l ⊕ r) (l ⊕ r) R).submatrix id Sum.inl

/-- The canonical inclusion of the right block into a direct-sum indexed matrix. -/
public def CFSG.identityBlockRightColumn {R l r : Type*} [Zero R] [One R]
    [DecidableEq (l ⊕ r)] : Matrix (l ⊕ r) r R :=
  (1 : Matrix (l ⊕ r) (l ⊕ r) R).submatrix id Sum.inr

/-- The canonical projection onto the left block from a direct-sum indexed matrix. -/
public def CFSG.identityBlockTopRow {R l r : Type*} [Zero R] [One R]
    [DecidableEq (l ⊕ r)] : Matrix l (l ⊕ r) R :=
  (1 : Matrix (l ⊕ r) (l ⊕ r) R).submatrix Sum.inl id

/-- The canonical projection onto the right block from a direct-sum indexed matrix. -/
public def CFSG.identityBlockBottomRow {R l r : Type*} [Zero R] [One R]
    [DecidableEq (l ⊕ r)] : Matrix r (l ⊕ r) R :=
  (1 : Matrix (l ⊕ r) (l ⊕ r) R).submatrix Sum.inr id

/-- The two canonical block inclusions assemble to the identity matrix. -/
public theorem CFSG.matrixOfIdentityBlockColumns_eq_one {R l r : Type*} [Zero R] [One R]
    [DecidableEq l] [DecidableEq r] :
    matrixOfBlockColumns (identityBlockLeftColumn (R := R) (l := l) (r := r))
      (identityBlockRightColumn (R := R) (l := l) (r := r)) = 1 := by
  ext i j
  cases j <;> rfl

/-- The two canonical block projections assemble to the identity matrix. -/
public theorem CFSG.matrixOfIdentityBlockRows_eq_one {R l r : Type*} [Zero R] [One R]
    [DecidableEq l] [DecidableEq r] :
    matrixOfBlockRows (identityBlockTopRow (R := R) (l := l) (r := r))
      (identityBlockBottomRow (R := R) (l := l) (r := r)) = 1 := by
  ext i j
  cases i <;> rfl

/-- Multiplying a two-block column by a two-block row gives the sum of the two
rectangular products. -/
public theorem CFSG.matrixOfBlockColumns_mul_matrixOfBlockRows
    {R l r : Type*} [NonUnitalNonAssocSemiring R] [Fintype l] [Fintype r]
    (left : Matrix (l ⊕ r) l R) (right : Matrix (l ⊕ r) r R)
    (top : Matrix l (l ⊕ r) R) (bottom : Matrix r (l ⊕ r) R) :
    matrixOfBlockColumns left right * matrixOfBlockRows top bottom =
      left * top + right * bottom := by
  ext i j
  rw [Matrix.mul_apply, Matrix.add_apply]
  cases i <;> cases j <;>
    simp [matrixOfBlockColumns, matrixOfBlockRows, Matrix.mul_apply,
      Fintype.sum_sum_type, Sum.elim]

/-- The upper-left block of a product by block rows and block columns. -/
public theorem CFSG.matrixOfBlockRows_mul_toBlocks₁₁
    {R l r : Type*} [NonUnitalNonAssocSemiring R] [Fintype (l ⊕ r)]
    (top : Matrix l (l ⊕ r) R) (bottom : Matrix r (l ⊕ r) R)
    (M : Matrix (l ⊕ r) (l ⊕ r) R)
    (left : Matrix (l ⊕ r) l R) (right : Matrix (l ⊕ r) r R) :
    (matrixOfBlockRows top bottom * M * matrixOfBlockColumns left right).toBlocks₁₁ =
      top * M * left := by
  ext i j
  change (((matrixOfBlockRows top bottom * M) * matrixOfBlockColumns left right)
      (Sum.inl i) (Sum.inl j)) = (((top * M) * left) i j)
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  simp [matrixOfBlockRows, matrixOfBlockColumns, Sum.elim]

/-- The lower-right block of a product by block rows and block columns. -/
public theorem CFSG.matrixOfBlockRows_mul_toBlocks₂₂
    {R l r : Type*} [NonUnitalNonAssocSemiring R] [Fintype (l ⊕ r)]
    (top : Matrix l (l ⊕ r) R) (bottom : Matrix r (l ⊕ r) R)
    (M : Matrix (l ⊕ r) (l ⊕ r) R)
    (left : Matrix (l ⊕ r) l R) (right : Matrix (l ⊕ r) r R) :
    (matrixOfBlockRows top bottom * M * matrixOfBlockColumns left right).toBlocks₂₂ =
      bottom * M * right := by
  ext i j
  change (((matrixOfBlockRows top bottom * M) * matrixOfBlockColumns left right)
      (Sum.inr i) (Sum.inr j)) = (((bottom * M) * right) i j)
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  simp [matrixOfBlockRows, matrixOfBlockColumns, Sum.elim]

/-- A block row built from matrices of two linear maps acts by applying the
corresponding map to the full vector. -/
public theorem CFSG.matrixOfBlockRows_toMatrix_mulVec
    {R l r : Type*} [CommSemiring R] [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r]
    (top : (l ⊕ r → R) →ₗ[R] (l → R))
    (bottom : (l ⊕ r → R) →ₗ[R] (r → R))
    (x : l ⊕ r → R) :
    Matrix.mulVec (matrixOfBlockRows (LinearMap.toMatrix' top) (LinearMap.toMatrix' bottom)) x =
      Sum.elim (top x) (bottom x) := by
  ext i
  cases i with
  | inl i =>
      change Matrix.mulVec (LinearMap.toMatrix' top) x i = top x i
      simp
  | inr i =>
      change Matrix.mulVec (LinearMap.toMatrix' bottom) x i = bottom x i
      simp

/-- A block column built from matrices of two linear maps acts by splitting the
input vector into its left and right coordinates. -/
public theorem CFSG.matrixOfBlockColumns_toMatrix_mulVec
    {R l r : Type*} [CommSemiring R] [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r]
    (left : (l → R) →ₗ[R] (l ⊕ r → R))
    (right : (r → R) →ₗ[R] (l ⊕ r → R))
    (x : l ⊕ r → R) :
    Matrix.mulVec (matrixOfBlockColumns (LinearMap.toMatrix' left) (LinearMap.toMatrix' right)) x =
      left (fun i => x (Sum.inl i)) + right (fun i => x (Sum.inr i)) := by
  let xl : l → R := fun i => x (Sum.inl i)
  let xr : r → R := fun i => x (Sum.inr i)
  calc
    Matrix.mulVec (matrixOfBlockColumns (LinearMap.toMatrix' left) (LinearMap.toMatrix' right)) x =
        Matrix.mulVec (LinearMap.toMatrix' left) xl +
          Matrix.mulVec (LinearMap.toMatrix' right) xr := by
      ext i
      change
        (∑ j : l ⊕ r,
            (Sum.elim (LinearMap.toMatrix' left i) (LinearMap.toMatrix' right i)) j * x j) =
          (Matrix.mulVec (LinearMap.toMatrix' left) xl +
            Matrix.mulVec (LinearMap.toMatrix' right) xr) i
      rw [Fintype.sum_sum_type]
      rfl
    _ = left xl + right xr := by
      simp [xl, xr]
