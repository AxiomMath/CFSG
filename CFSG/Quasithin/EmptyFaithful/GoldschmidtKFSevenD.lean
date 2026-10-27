module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.SBd19F

open Matrix

variable {K : Type} [Field K]

@[expose] def colMat (S : Matrix (Fin 3) (Fin 3) K) (σ : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun r k => (if r = k then 1 else 0) + σ k * S r k

theorem sum_det_colMat (S : Matrix (Fin 3) (Fin 3) K) :
    (colMat S ![1, 1, 1]).det + (colMat S ![1, 1, -1]).det + (colMat S ![1, -1, 1]).det +
      (colMat S ![1, -1, -1]).det + (colMat S ![-1, 1, 1]).det + (colMat S ![-1, 1, -1]).det +
      (colMat S ![-1, -1, 1]).det + (colMat S ![-1, -1, -1]).det = 8 := by
  simp [colMat, det_fin_three]
  ring

theorem mul_colMat {S : Matrix (Fin 3) (Fin 3) K} (hS : S * S = 1) {σ : Fin 3 → K}
    (hσ : ∀ k, σ k = 1 ∨ σ k = -1) :
    S * colMat S σ = colMat S σ * Matrix.diagonal σ := by
  ext r k
  have h1 := congrFun (congrFun hS r) k
  have hk : σ k * σ k = 1 := by rcases hσ k with h | h <;> rw [h] <;> ring
  simp only [colMat, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Matrix.mul_apply, Matrix.one_apply] at h1
  have e : ∑ l, S r l * ((if l = k then 1 else 0) + σ k * S l k) =
      S r k + σ k * ∑ l, S r l * S l k := by
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [e, h1]
  by_cases hrk : r = k
  · subst hrk
    simp
    linear_combination (-(S r r)) * hk
  · simp [hrk]
    linear_combination (-(S r k)) * hk

theorem mul_submatrix {S M : Matrix (Fin 3) (Fin 3) K} {σ : Fin 3 → K}
    (h : S * M = M * Matrix.diagonal σ) (π : Equiv.Perm (Fin 3)) :
    S * M.submatrix id π = M.submatrix id π * Matrix.diagonal (σ ∘ π) := by
  ext r k
  have h1 : (S * M) r (π k) = (M * Matrix.diagonal σ) r (π k) := by rw [h]
  rw [Matrix.mul_diagonal] at h1
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Function.comp_apply, id] at h1 ⊢
  exact h1

theorem eigenbasis_aux {S : Matrix (Fin 3) (Fin 3) K} (hS : S * S = 1) {σ : Fin 3 → K}
    (hσ : ∀ k, σ k = 1 ∨ σ k = -1) (hdet : (colMat S σ).det ≠ 0) (π : Equiv.Perm (Fin 3))
    (hπ : σ (π 0) = σ (π 1)) :
    ∃ (B : Matrix (Fin 3) (Fin 3) K) (ε ε' : K), B.det ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧
      (ε' = 1 ∨ ε' = -1) ∧ S * B = B * Matrix.diagonal ![ε, ε, ε'] := by
  refine ⟨(colMat S σ).submatrix id π, σ (π 0), σ (π 2), ?_, hσ _, hσ _, ?_⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hdet
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  · have h1 := mul_submatrix (mul_colMat hS hσ) π
    convert h1 using 2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hπ]

theorem exists_eigenbasis_of_involution (h2 : (2 : K) ≠ 0) {S : Matrix (Fin 3) (Fin 3) K}
    (hS : S * S = 1) :
    ∃ (B : Matrix (Fin 3) (Fin 3) K) (ε ε' : K), B.det ≠ 0 ∧ (ε = 1 ∨ ε = -1) ∧
      (ε' = 1 ∨ ε' = -1) ∧ S * B = B * Matrix.diagonal ![ε, ε, ε'] := by
  have h8 : (8 : K) ≠ 0 := by
    have : (8 : K) = 2 * 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hsum := sum_det_colMat S
  by_cases d1 : (colMat S ![1, 1, 1]).det = 0
  · by_cases d2 : (colMat S ![1, 1, -1]).det = 0
    · by_cases d3 : (colMat S ![1, -1, 1]).det = 0
      · by_cases d4 : (colMat S ![1, -1, -1]).det = 0
        · by_cases d5 : (colMat S ![-1, 1, 1]).det = 0
          · by_cases d6 : (colMat S ![-1, 1, -1]).det = 0
            · by_cases d7 : (colMat S ![-1, -1, 1]).det = 0
              · by_cases d8 : (colMat S ![-1, -1, -1]).det = 0
                · exact absurd (by rw [← hsum, d1, d2, d3, d4, d5, d6, d7, d8]; ring) h8
                · exact eigenbasis_aux hS (σ := ![-1, -1, -1]) (by intro k; fin_cases k <;> simp)
                    d8 1 (by simp)
              · exact eigenbasis_aux hS (σ := ![-1, -1, 1]) (by intro k; fin_cases k <;> simp)
                  d7 1 (by simp)
            · exact eigenbasis_aux hS (σ := ![-1, 1, -1]) (by intro k; fin_cases k <;> simp)
                d6 (Equiv.swap 1 2) (by simp [Equiv.swap_apply_of_ne_of_ne])
          · exact eigenbasis_aux hS (σ := ![-1, 1, 1]) (by intro k; fin_cases k <;> simp)
              d5 (finRotate 3) (by simp)
        · exact eigenbasis_aux hS (σ := ![1, -1, -1]) (by intro k; fin_cases k <;> simp)
            d4 (finRotate 3) (by simp)
      · exact eigenbasis_aux hS (σ := ![1, -1, 1]) (by intro k; fin_cases k <;> simp)
          d3 (Equiv.swap 1 2) (by simp [Equiv.swap_apply_of_ne_of_ne])
    · exact eigenbasis_aux hS (σ := ![1, 1, -1]) (by intro k; fin_cases k <;> simp)
        d2 1 (by simp)
  · exact eigenbasis_aux hS (σ := ![1, 1, 1]) (by intro k; fin_cases k <;> simp) d1 1 (by simp)

end CFSG.Quasithin.SBd19F
