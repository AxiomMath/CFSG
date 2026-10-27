module

public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix

@[expose] def cM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def fM : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

theorem cM_pow_seven : cM ^ 7 = 1 := by decide +kernel

theorem cM_ne_one : cM ≠ 1 := by decide +kernel

theorem cM_det : cM.det = 1 := by decide +kernel

theorem fM_det : fM.det = 1 := by decide +kernel

theorem fM_mul_cM : fM * cM = cM ^ 2 * fM := by decide +kernel

theorem comm_cM (P : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : P * cM = cM * P) :
    P = 0 ∨ ∃ i : ℕ, P = cM ^ i := by
  have key : ∀ P : Matrix (Fin 3) (Fin 3) (ZMod 2), P * cM = cM * P →
      P = 0 ∨ ∃ i : Fin 7, P = cM ^ (i : ℕ) := by decide +kernel
  rcases key P h with h0 | ⟨i, hi⟩
  · exact Or.inl h0
  · exact Or.inr ⟨i, hi⟩

theorem intertwine_zero (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : Q * cM ^ 3 = cM * Q) :
    Q = 0 := by
  have key : ∀ Q : Matrix (Fin 3) (Fin 3) (ZMod 2), Q * cM ^ 3 = cM * Q → Q = 0 := by
    decide +kernel
  exact key Q h

theorem intertwine_zero' (Q : Matrix (Fin 3) (Fin 3) (ZMod 2)) (h : Q * cM = cM ^ 3 * Q) :
    Q = 0 := by
  have key : ∀ Q : Matrix (Fin 3) (Fin 3) (ZMod 2), Q * cM = cM ^ 3 * Q → Q = 0 := by
    decide +kernel
  exact key Q h

theorem exists_inv_cM_sub_one : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M * (cM - 1) = 1 ∧ (cM - 1) * M = 1 := by decide +kernel

theorem eq_zero_of_cM_mul {m : Type} [Fintype m] (Q : Matrix (Fin 3) m (ZMod 2))
    (h : cM * Q = Q) : Q = 0 := by
  obtain ⟨M, hM, -⟩ := exists_inv_cM_sub_one
  have h1 : (cM - 1) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  calc Q = (M * (cM - 1)) * Q := by rw [hM, Matrix.one_mul]
    _ = M * ((cM - 1) * Q) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h1, Matrix.mul_zero]

theorem eq_zero_of_mul_cM {m : Type} [Fintype m] (R : Matrix m (Fin 3) (ZMod 2))
    (h : R * cM = R) : R = 0 := by
  obtain ⟨M, -, hM⟩ := exists_inv_cM_sub_one
  have h1 : R * (cM - 1) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  calc R = R * ((cM - 1) * M) := by rw [hM, Matrix.mul_one]
    _ = (R * (cM - 1)) * M := (Matrix.mul_assoc _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_mul]

theorem commute_cM_of_commute_cM_pow_three (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : P * cM ^ 3 = cM ^ 3 * P) : P * cM = cM * P := by
  have hc : cM = (cM ^ 3) ^ 5 := by
    rw [← pow_mul]
    have : cM ^ 15 = cM := by
      have h7 : cM ^ 15 = (cM ^ 7) ^ 2 * cM := by rw [← pow_mul, ← pow_succ]
      rw [h7, cM_pow_seven, one_pow, one_mul]
    simpa using this.symm
  have hcom : Commute P (cM ^ 3) := h
  rw [hc]
  exact (hcom.pow_right 5).eq

theorem exists_inv_cM_pow_three_sub_one : ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2),
    M * (cM ^ 3 - 1) = 1 ∧ (cM ^ 3 - 1) * M = 1 := by decide +kernel

theorem eq_zero_of_mul_eq_self {X m : Type} [Fintype X] [DecidableEq X] [Fintype m]
    {B : Matrix X X (ZMod 2)} (hB : ∃ N : Matrix X X (ZMod 2), N * (B - 1) = 1)
    {Q : Matrix X m (ZMod 2)} (h : B * Q = Q) : Q = 0 := by
  obtain ⟨N, hN⟩ := hB
  have h1 : (B - 1) * Q = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h, sub_self]
  calc Q = (N * (B - 1)) * Q := by rw [hN, Matrix.one_mul]
    _ = N * ((B - 1) * Q) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h1, Matrix.mul_zero]

theorem eq_zero_of_mul_eq_self' {X m : Type} [Fintype X] [DecidableEq X] [Fintype m]
    {B : Matrix X X (ZMod 2)} (hB : ∃ N : Matrix X X (ZMod 2), (B - 1) * N = 1)
    {R : Matrix m X (ZMod 2)} (h : R * B = R) : R = 0 := by
  obtain ⟨N, hN⟩ := hB
  have h1 : R * (B - 1) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, h, sub_self]
  calc R = R * ((B - 1) * N) := by rw [hN, Matrix.mul_one]
    _ = (R * (B - 1)) * N := (Matrix.mul_assoc _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_mul]

theorem fromBlocks_sub_one {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (D₀ : Matrix X X (ZMod 2)) (D₁ : Matrix Y Y (ZMod 2)) :
    (fromBlocks D₀ 0 0 D₁ - 1 : Matrix (X ⊕ Y) (X ⊕ Y) (ZMod 2)) =
      fromBlocks (D₀ - 1) 0 0 (D₁ - 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply]

theorem fromBlocks_sub_one_inv {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {D₀ M₀ : Matrix X X (ZMod 2)} {D₁ M₁ : Matrix Y Y (ZMod 2)}
    (h₀ : M₀ * (D₀ - 1) = 1) (h₁ : M₁ * (D₁ - 1) = 1) :
    fromBlocks M₀ 0 0 M₁ * (fromBlocks D₀ 0 0 D₁ - 1) = 1 := by
  rw [fromBlocks_sub_one]
  simp [fromBlocks_multiply, h₀, h₁]

theorem fromBlocks_sub_one_inv' {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {D₀ M₀ : Matrix X X (ZMod 2)} {D₁ M₁ : Matrix Y Y (ZMod 2)}
    (h₀ : (D₀ - 1) * M₀ = 1) (h₁ : (D₁ - 1) * M₁ = 1) :
    (fromBlocks D₀ 0 0 D₁ - 1) * fromBlocks M₀ 0 0 M₁ = 1 := by
  rw [fromBlocks_sub_one]
  simp [fromBlocks_multiply, h₀, h₁]

end CFSG.RankThree.PartOne.MB3
