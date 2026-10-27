module

public import CFSG.LocalAnalysis.StandardType.SpFixedNorm

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix

variable {F : Type} [Field F] {n m : ℕ}

theorem fromBlocks_neg_diag (A D : Matrix (Fin n) (Fin n) F) :
    fromBlocks (-A) 0 0 (-D) = -fromBlocks A 0 0 D := by
  simp [fromBlocks_neg]

theorem gram_transpose : (gram F n)ᵀ = -gram F n := by
  unfold gram
  rw [fromBlocks_transpose]
  simp only [transpose_zero, transpose_one, transpose_neg, neg_zero]
  rw [fromBlocks_neg]
  simp

theorem gram_mul_gram : gram F n * gram F n = -1 := by
  unfold gram
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [fromBlocks_neg_diag, fromBlocks_one]

@[expose] def dualMat (B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F) :
    Matrix (Fin m ⊕ Fin m) (Fin n ⊕ Fin n) F :=
  -(gram F m * Bᵀ * gram F n)

structure IsFixedBasis (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F) : Prop where
  mul_self : N * N = N
  adjoint : Nᵀ * gram F n = gram F n * N
  form : Bᵀ * gram F n * B = gram F m
  fixed : N * B = B
  span : ∀ x : Fin n ⊕ Fin n → F, ∃ c : Fin m ⊕ Fin m → F, N *ᵥ x = B *ᵥ c

theorem dualMat_mul_self {B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F}
    (hB : Bᵀ * gram F n * B = gram F m) : dualMat B * B = 1 := by
  unfold dualMat
  rw [Matrix.neg_mul]
  rw [show (gram F m * Bᵀ * gram F n) * B = gram F m * (Bᵀ * gram F n * B) by
        simp only [Matrix.mul_assoc]]
  rw [hB, gram_mul_gram, neg_neg]

theorem dualMat_transpose (B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F) :
    (dualMat B)ᵀ = -(gram F n * B * gram F m) := by
  unfold dualMat
  rw [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.transpose_transpose, gram_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    Matrix.mul_assoc]

variable {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
  {B : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) F}

theorem IsFixedBasis.dualMat_mul_fixedNorm (h : IsFixedBasis N B) : dualMat B * N = dualMat B := by
  unfold dualMat
  rw [Matrix.neg_mul]
  congr 1
  calc (gram F m * Bᵀ * gram F n) * N
      = gram F m * Bᵀ * (gram F n * N) := by simp only [Matrix.mul_assoc]
    _ = gram F m * Bᵀ * (Nᵀ * gram F n) := by rw [← h.adjoint]
    _ = gram F m * (Bᵀ * Nᵀ) * gram F n := by simp only [Matrix.mul_assoc]
    _ = gram F m * (N * B)ᵀ * gram F n := by rw [Matrix.transpose_mul]
    _ = gram F m * Bᵀ * gram F n := by rw [h.fixed]

theorem IsFixedBasis.self_mul_dualMat (h : IsFixedBasis N B) : B * dualMat B = N := by
  rw [Matrix.ext_iff_mulVec]
  intro x
  obtain ⟨c, hc⟩ := h.span x
  have hfix : dualMat B *ᵥ x = dualMat B *ᵥ (N *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, h.dualMat_mul_fixedNorm]
  have hd : dualMat B *ᵥ x = c := by
    rw [hfix, hc, Matrix.mulVec_mulVec, dualMat_mul_self h.form, Matrix.one_mulVec]
  calc (B * dualMat B) *ᵥ x
      = B *ᵥ (dualMat B *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = B *ᵥ c := by rw [hd]
    _ = N *ᵥ x := hc.symm

theorem IsFixedBasis.dualMat_transpose_mul_gram_mul (h : IsFixedBasis N B) :
    (dualMat B)ᵀ * gram F m * dualMat B = gram F n * N := by
  have h1 : (dualMat B)ᵀ * gram F m = gram F n * B := by
    rw [dualMat_transpose, Matrix.neg_mul]
    have h2 : (gram F n * B * gram F m) * gram F m = -(gram F n * B) := by
      calc (gram F n * B * gram F m) * gram F m
          = gram F n * B * (gram F m * gram F m) := by simp only [Matrix.mul_assoc]
        _ = -(gram F n * B) := by rw [gram_mul_gram, Matrix.mul_neg, Matrix.mul_one]
    rw [h2, neg_neg]
  rw [h1, ← h.self_mul_dualMat]
  simp only [Matrix.mul_assoc]

end SpFixed

end CFSG.StandardType
