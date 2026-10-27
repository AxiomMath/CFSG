module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.RepresentationTheory.SzMartineau

open Matrix

variable {K : Type*} [CommRing K] [CharP K 2]

@[expose] def szX₀ : Matrix (Fin 4) (Fin 4) K :=
  !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def szJ : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[simp] lemma szX₀_sq :
    szX₀ ^ 2 = (!![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) K) := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szX₀, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

@[simp] lemma szX₀_cube :
    szX₀ ^ 3 = (!![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) K) := by
  have h3 : szX₀ ^ 3 = (szX₀ ^ 2 * szX₀ : Matrix (Fin 4) (Fin 4) K) := by
    rw [show (3:ℕ) = 2 + 1 by norm_num, pow_succ]
  rw [h3, szX₀_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [szX₀, Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

local macro "char2_norm" : tactic =>
  `(tactic| (simp only [szX₀_sq, szX₀_cube] <;>
    simp [szX₀, szJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_apply, dotProduct,
      CharTwo.add_self_eq_zero] <;>
    ring_nf <;> simp only [CharTwo.ofNat_eq_mod] <;> norm_num))

local macro "char2_finish" : tactic =>
  `(tactic| (ring_nf <;> simp only [CharTwo.ofNat_eq_mod] <;> norm_num))

private lemma h4_entry (A : Matrix (Fin 4) (Fin 4) K)
    (h4 : A * szX₀ ^ 3 + szX₀ * A * szX₀ ^ 2 + szX₀ ^ 2 * A * szX₀ +
      szX₀ ^ 3 * A = 0) (i j : Fin 4) :
    ((A * szX₀ ^ 3 + szX₀ * A * szX₀ ^ 2 + szX₀ ^ 2 * A * szX₀ +
      szX₀ ^ 3 * A : Matrix (Fin 4) (Fin 4) K)) i j = 0 := by
  simpa using congrFun (congrFun h4 i) j

private lemma hC_entry (A : Matrix (Fin 4) (Fin 4) K)
    (hC : szJ * A * szJ = szX₀ * szJ * szX₀ * A + szX₀ * szJ * A * szX₀ +
      A * szJ * szX₀ ^ 2) (i j : Fin 4) :
    ((szJ * A * szJ + (szX₀ * szJ * szX₀ * A + szX₀ * szJ * A * szX₀ +
      A * szJ * szX₀ ^ 2) : Matrix (Fin 4) (Fin 4) K)) i j = 0 := by
  have h := congrFun (congrFun hC i) j
  rw [Matrix.add_apply, h, CharTwo.add_self_eq_zero]

private lemma relations (A : Matrix (Fin 4) (Fin 4) K)
    (h4 : A * szX₀ ^ 3 + szX₀ * A * szX₀ ^ 2 + szX₀ ^ 2 * A * szX₀ +
      szX₀ ^ 3 * A = 0)
    (hC : szJ * A * szJ = szX₀ * szJ * szX₀ * A + szX₀ * szJ * A * szX₀ +
      A * szJ * szX₀ ^ 2) :
    (A 0 0 + A 1 1 + A 2 2 + A 3 3 = 0) ∧
    (A 0 1 + A 2 1 + A 2 2 + A 2 3 + A 3 1 + A 3 2 + A 3 3 = 0) ∧
    (A 0 2 + A 2 2 + A 3 1 + A 3 2 + A 3 3 = 0) ∧
    (A 0 3 + A 2 1 + A 3 1 + A 3 2 + A 3 3 = 0) ∧
    (A 1 0 + A 2 1 + A 3 1 + A 3 2 = 0) ∧
    (A 1 2 + A 3 1 + A 3 2 + A 3 3 = 0) ∧
    (A 1 3 + A 2 1 + A 2 3 + A 3 2 = 0) ∧
    (A 2 0 + A 3 1 = 0) ∧ (A 3 0 = 0) := by
  have e400 := h4_entry A h4 0 0
  have e401 := h4_entry A h4 0 1
  have e402 := h4_entry A h4 0 2
  have e403 := h4_entry A h4 0 3
  have eC00 := hC_entry A hC 0 0
  have eC01 := hC_entry A hC 0 1
  have eC02 := hC_entry A hC 0 2
  have eC03 := hC_entry A hC 0 3
  have eC10 := hC_entry A hC 1 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (norm := char2_norm) e401 + e402 + e403
  · linear_combination (norm := char2_norm) e400 + eC00 + eC03 + eC10
  · linear_combination (norm := char2_norm) e402 + e403 + eC01
  · linear_combination (norm := char2_norm) e400 + e402 + eC00
  · linear_combination (norm := char2_norm) e400 + e402
  · linear_combination (norm := char2_norm) e400 + e402 + eC00 + eC02
  · linear_combination (norm := char2_norm) e400 + e401 + e402 + eC10
  · linear_combination (norm := char2_norm) e400 + e401
  · linear_combination (norm := char2_norm) e400

private lemma exists_of_relations (A : Matrix (Fin 4) (Fin 4) K)
    (r0 : A 0 0 + A 1 1 + A 2 2 + A 3 3 = 0)
    (r1 : A 0 1 + A 2 1 + A 2 2 + A 2 3 + A 3 1 + A 3 2 + A 3 3 = 0)
    (r2 : A 0 2 + A 2 2 + A 3 1 + A 3 2 + A 3 3 = 0)
    (r3 : A 0 3 + A 2 1 + A 3 1 + A 3 2 + A 3 3 = 0)
    (r4 : A 1 0 + A 2 1 + A 3 1 + A 3 2 = 0)
    (r5 : A 1 2 + A 3 1 + A 3 2 + A 3 3 = 0)
    (r6 : A 1 3 + A 2 1 + A 2 3 + A 3 2 = 0)
    (r7 : A 2 0 + A 3 1 = 0) (r8 : A 3 0 = 0) :
    ∃ X : Matrix (Fin 4) (Fin 4) K, szJ * X = X * szJ ∧ A = szX₀ * X + X * szX₀ := by
  let X : Matrix (Fin 4) (Fin 4) K :=
    !![A 0 1 + A 3 2, A 1 2, A 3 2, A 2 0;
       A 0 0 + A 2 0, 0, A 0 2, A 2 1 + A 3 2;
       A 2 1 + A 3 2, A 0 2, 0, A 0 0 + A 2 0;
       A 2 0, A 3 2, A 1 2, A 0 1 + A 3 2]
  refine ⟨X, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, szJ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_apply, dotProduct]
  · ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [X, szX₀, Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul_apply, dotProduct,
        CharTwo.add_self_eq_zero]
    all_goals
        first
        | (linear_combination (norm := char2_finish); done)
        | (linear_combination (norm := char2_finish) (r3 + r5); done)
        | (linear_combination (norm := char2_finish) (r4 + r7); done)
        | (linear_combination (norm := char2_finish) (r0 + r2 + r7); done)
        | (linear_combination (norm := char2_finish) (r1 + r2 + r6); done)
        | (linear_combination (norm := char2_finish) (r2 + r5); done)
        | (linear_combination (norm := char2_finish) (r1 + r2); done)
        | (linear_combination (norm := char2_finish) r8; done)
        | (linear_combination (norm := char2_finish) r7; done)
        | (linear_combination (norm := char2_finish) (r5 + r7); done)

theorem exists_szTwo_coboundary (A : Matrix (Fin 4) (Fin 4) K)
    (h4 : A * szX₀ ^ 3 + szX₀ * A * szX₀ ^ 2 + szX₀ ^ 2 * A * szX₀ +
      szX₀ ^ 3 * A = 0)
    (hC : szJ * A * szJ = szX₀ * szJ * szX₀ * A + szX₀ * szJ * A * szX₀ +
      A * szJ * szX₀ ^ 2) :
    ∃ X : Matrix (Fin 4) (Fin 4) K, szJ * X = X * szJ ∧ A = szX₀ * X + X * szX₀ := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8⟩ := relations A h4 hC
  exact exists_of_relations A r0 r1 r2 r3 r4 r5 r6 r7 r8

end CFSG.RepresentationTheory.SzMartineau
