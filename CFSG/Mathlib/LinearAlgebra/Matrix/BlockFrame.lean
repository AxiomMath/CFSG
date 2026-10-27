module

public import CFSG.Mathlib.LinearAlgebra.Matrix.OrthogonalFrame

public section

namespace Matrix

variable {n : ℕ} {F : Type*} [Field F]

@[expose] def orbitMatrix (B : Matrix (Fin n) (Fin n) F) (u : Fin n → F) :
    Matrix (Fin n) (Fin 3) F :=
  Matrix.of fun k i => ((B ^ (i : ℕ)) *ᵥ u) k

@[expose] def cubicCompanion (c : F) : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, c; 1, 0, 0; 0, 1, 0]

private lemma cq1_mul_mul_mul_mul {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (X : Matrix a b F) (Y : Matrix b c F) (Z : Matrix c d F) (W : Matrix d e F) :
    (X * Y) * (Z * W) = X * (Y * Z) * W := by
  calc (X * Y) * (Z * W) = X * (Y * (Z * W)) := Matrix.mul_assoc X Y (Z * W)
    _ = X * ((Y * Z) * W) := by rw [Matrix.mul_assoc Y Z W]
    _ = X * (Y * Z) * W := (Matrix.mul_assoc X (Y * Z) W).symm

private lemma cq1_mul_orbitMatrix_apply (B : Matrix (Fin n) (Fin n) F) (u : Fin n → F)
    (k : Fin n) (j : Fin 3) :
    (B * orbitMatrix B u) k j = ((B ^ ((j : ℕ) + 1)) *ᵥ u) k := by
  show (B *ᵥ ((B ^ (j : ℕ)) *ᵥ u)) k = ((B ^ ((j : ℕ) + 1)) *ᵥ u) k
  rw [Matrix.mulVec_mulVec, ← pow_succ']

theorem mul_orbitMatrix {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (u : Fin n → F) :
    B * orbitMatrix B u = orbitMatrix B u * cubicCompanion c := by
  ext k j
  fin_cases j
  · rw [cq1_mul_orbitMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three]
    simp [orbitMatrix, cubicCompanion, Matrix.one_mulVec]
  · rw [cq1_mul_orbitMatrix_apply, Matrix.mul_apply, Fin.sum_univ_three]
    simp [orbitMatrix, cubicCompanion, Matrix.one_mulVec]
  · rw [cq1_mul_orbitMatrix_apply, hB3, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.mul_apply, Fin.sum_univ_three]
    simp [orbitMatrix, cubicCompanion, Matrix.one_mulVec]
    ring

structure BlockFrame (B : Matrix (Fin n) (Fin n) F) (C : Matrix (Fin 3) (Fin 3) F)
    (U₁ U₂ : Matrix (Fin n) (Fin 3) F) (V₁ V₂ : Matrix (Fin 3) (Fin n) F) : Prop where
  v₁u₁ : V₁ * U₁ = 1
  v₂u₂ : V₂ * U₂ = 1
  v₁u₂ : V₁ * U₂ = 0
  v₂u₁ : V₂ * U₁ = 0
  bu₁ : B * U₁ = U₁ * C
  bu₂ : B * U₂ = U₂ * C
  v₁b : V₁ * B = C * V₁
  v₂b : V₂ * B = C * V₂

@[expose] def BlockFrame.swapMatrix (U₁ U₂ : Matrix (Fin n) (Fin 3) F)
    (V₁ V₂ : Matrix (Fin 3) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  1 - U₁ * V₁ - U₂ * V₂ + U₂ * V₁ + U₁ * V₂

section BlockFrame

variable {B : Matrix (Fin n) (Fin n) F} {C : Matrix (Fin 3) (Fin 3) F}
  {U₁ U₂ : Matrix (Fin n) (Fin 3) F} {V₁ V₂ : Matrix (Fin 3) (Fin n) F}

theorem BlockFrame.table_P (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    (U₁ * V₁) * (U₁ * V₁) = U₁ * V₁ ∧ (U₂ * V₂) * (U₂ * V₂) = U₂ * V₂ ∧
      (U₁ * V₁) * (U₂ * V₂) = 0 ∧ (U₂ * V₂) * (U₁ * V₁) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [cq1_mul_mul_mul_mul, hF.v₁u₁, hF.v₂u₂, hF.v₁u₂, hF.v₂u₁,
      Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero]

theorem BlockFrame.table_PE (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    (U₁ * V₁) * (U₂ * V₁) = 0 ∧ (U₂ * V₁) * (U₁ * V₁) = U₂ * V₁ ∧
      (U₂ * V₂) * (U₂ * V₁) = U₂ * V₁ ∧ (U₂ * V₁) * (U₂ * V₂) = 0 ∧
      (U₁ * V₁) * (U₁ * V₂) = U₁ * V₂ ∧ (U₁ * V₂) * (U₁ * V₁) = 0 ∧
      (U₂ * V₂) * (U₁ * V₂) = 0 ∧ (U₁ * V₂) * (U₂ * V₂) = U₁ * V₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [cq1_mul_mul_mul_mul, hF.v₁u₁, hF.v₂u₂, hF.v₁u₂, hF.v₂u₁,
      Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero]

theorem BlockFrame.table_EG (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    (U₂ * V₁) * (U₂ * V₁) = 0 ∧ (U₁ * V₂) * (U₁ * V₂) = 0 ∧
      (U₂ * V₁) * (U₁ * V₂) = U₂ * V₂ ∧ (U₁ * V₂) * (U₂ * V₁) = U₁ * V₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [cq1_mul_mul_mul_mul, hF.v₁u₁, hF.v₂u₂, hF.v₁u₂, hF.v₂u₁,
      Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero]

theorem BlockFrame.comm_table (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    B * (U₁ * V₁) = (U₁ * V₁) * B ∧ B * (U₂ * V₂) = (U₂ * V₂) * B ∧
      B * (U₂ * V₁) = (U₂ * V₁) * B ∧ B * (U₁ * V₂) = (U₁ * V₂) * B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc B U₁ V₁, hF.bu₁, Matrix.mul_assoc U₁ C V₁, ← hF.v₁b,
      ← Matrix.mul_assoc U₁ V₁ B]
  · rw [← Matrix.mul_assoc B U₂ V₂, hF.bu₂, Matrix.mul_assoc U₂ C V₂, ← hF.v₂b,
      ← Matrix.mul_assoc U₂ V₂ B]
  · rw [← Matrix.mul_assoc B U₂ V₁, hF.bu₂, Matrix.mul_assoc U₂ C V₁, ← hF.v₁b,
      ← Matrix.mul_assoc U₂ V₁ B]
  · rw [← Matrix.mul_assoc B U₁ V₂, hF.bu₁, Matrix.mul_assoc U₁ C V₂, ← hF.v₂b,
      ← Matrix.mul_assoc U₁ V₂ B]

theorem BlockFrame.ne_zero (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    U₁ * V₁ ≠ 0 ∧ U₂ * V₂ ≠ 0 := by
  constructor
  · intro h
    have h1 : (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [← hF.v₁u₁]
      calc V₁ * U₁ = (V₁ * U₁) * (V₁ * U₁) := by rw [hF.v₁u₁, Matrix.one_mul]
        _ = V₁ * (U₁ * V₁) * U₁ := cq1_mul_mul_mul_mul V₁ U₁ V₁ U₁
        _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    exact one_ne_zero h1
  · intro h
    have h1 : (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [← hF.v₂u₂]
      calc V₂ * U₂ = (V₂ * U₂) * (V₂ * U₂) := by rw [hF.v₂u₂, Matrix.one_mul]
        _ = V₂ * (U₂ * V₂) * U₂ := cq1_mul_mul_mul_mul V₂ U₂ V₂ U₂
        _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    exact one_ne_zero h1

private lemma cq1_swap_mul_P₁ (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    BlockFrame.swapMatrix U₁ U₂ V₁ V₂ * (U₁ * V₁) = U₂ * V₁ := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hP₁E, hEP₁, hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂⟩ := hF.table_PE
  simp only [BlockFrame.swapMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
    hP₁, hP₂P₁, hEP₁, hGP₁]
  abel

private lemma cq1_swap_mul_P₂ (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    BlockFrame.swapMatrix U₁ U₂ V₁ V₂ * (U₂ * V₂) = U₁ * V₂ := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hP₁E, hEP₁, hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂⟩ := hF.table_PE
  simp only [BlockFrame.swapMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul,
    hP₁P₂, hP₂, hEP₂, hGP₂]
  abel

private lemma cq1_P₂_mul_swap (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    (U₂ * V₂) * BlockFrame.swapMatrix U₁ U₂ V₁ V₂ = U₂ * V₁ := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hP₁E, hEP₁, hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂⟩ := hF.table_PE
  simp only [BlockFrame.swapMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one,
    hP₂P₁, hP₂, hP₂E, hP₂G]
  abel

private lemma cq1_P₁_mul_swap (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    (U₁ * V₁) * BlockFrame.swapMatrix U₁ U₂ V₁ V₂ = U₁ * V₂ := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hP₁E, hEP₁, hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂⟩ := hF.table_PE
  simp only [BlockFrame.swapMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one,
    hP₁P₂, hP₁, hP₁E, hP₁G]
  abel

private lemma cq1_swap_mul_swap (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    BlockFrame.swapMatrix U₁ U₂ V₁ V₂ * BlockFrame.swapMatrix U₁ U₂ V₁ V₂ = 1 := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hP₁E, hEP₁, hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂⟩ := hF.table_PE
  obtain ⟨hEE, hGG, hEG, hGE⟩ := hF.table_EG
  simp only [BlockFrame.swapMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_sub,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hP₁, hP₂, hP₁P₂, hP₂P₁, hP₁E, hEP₁,
    hP₂E, hEP₂, hP₁G, hGP₁, hP₂G, hGP₂, hEE, hGG, hEG, hGE]
  abel

private lemma cq1_comm_swap (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    B * BlockFrame.swapMatrix U₁ U₂ V₁ V₂ = BlockFrame.swapMatrix U₁ U₂ V₁ V₂ * B := by
  obtain ⟨hc₁, hc₂, hcE, hcG⟩ := hF.comm_table
  simp only [BlockFrame.swapMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, hc₁, hc₂, hcE, hcG]

theorem BlockFrame.isOrthogonalFrame (hF : BlockFrame B C U₁ U₂ V₁ V₂) :
    IsOrthogonalFrame B (U₁ * V₁) (U₂ * V₂) (BlockFrame.swapMatrix U₁ U₂ V₁ V₂) := by
  obtain ⟨hP₁, hP₂, hP₁P₂, hP₂P₁⟩ := hF.table_P
  obtain ⟨hne₁, hne₂⟩ := hF.ne_zero
  obtain ⟨hc₁, hc₂, hcE, hcG⟩ := hF.comm_table
  refine ⟨hP₁, hP₂, hP₁P₂, hP₂P₁, hne₁, hne₂, hc₁, hc₂, ?_, ?_, ?_, ?_⟩
  · exact cq1_comm_swap hF
  · exact cq1_swap_mul_swap hF
  · exact (cq1_swap_mul_P₁ hF).trans (cq1_P₂_mul_swap hF).symm
  · exact (cq1_swap_mul_P₂ hF).trans (cq1_P₁_mul_swap hF).symm

end BlockFrame

end Matrix
