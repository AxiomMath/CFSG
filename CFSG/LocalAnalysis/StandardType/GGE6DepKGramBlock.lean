module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.StandardType

namespace E6Dep

open Matrix

private lemma gram6_transpose : gram6ᵀ = gram6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram6, Matrix.transpose_apply]

private lemma gram6_symm (i j : Fin 6) : gram6 i j = gram6 j i := by
  have h := congr_fun (congr_fun gram6_transpose j) i
  simpa [Matrix.transpose_apply] using h

private lemma hJ_zero : hJ (0 : Fin 5) = Pi.single (0 : Fin 6) (1 : ZMod 3) := by
  ext k
  fin_cases k <;> simp [hJ, Pi.single]

private lemma hJ_one : hJ (1 : Fin 5) = Pi.single (1 : Fin 6) (1 : ZMod 3) := by
  ext k
  fin_cases k <;> simp [hJ, Pi.single]

private lemma hJ_two : hJ (2 : Fin 5) = Pi.single (2 : Fin 6) (1 : ZMod 3) := by
  ext k
  fin_cases k <;> simp [hJ, Pi.single]

private lemma hJ_three : hJ (3 : Fin 5) = Pi.single (3 : Fin 6) (1 : ZMod 3) := by
  ext k
  fin_cases k <;> simp [hJ, Pi.single]

private lemma kY_single (c : ZMod 3) :
    kY c = Pi.single (4 : Fin 6) (1 : ZMod 3) + c • Pi.single (5 : Fin 6) (1 : ZMod 3) := by
  ext k
  fin_cases k <;> simp [kY, Pi.single]

private lemma pullback_dot (M : Mat6) (u e : Vec6) :
    u ⬝ᵥ (Mᵀ * gram6 * M) *ᵥ e = (M *ᵥ u) ⬝ᵥ gram6 *ᵥ (M *ᵥ e) := by
  calc u ⬝ᵥ (Mᵀ * gram6 * M) *ᵥ e
      = u ⬝ᵥ Mᵀ *ᵥ (gram6 *ᵥ (M *ᵥ e)) := by
          rw [← Matrix.mulVec_mulVec]
          rw [← Matrix.mulVec_mulVec]
    _ = u ᵥ* Mᵀ ⬝ᵥ (gram6 *ᵥ (M *ᵥ e)) := by
          rw [Matrix.dotProduct_mulVec]
    _ = (M *ᵥ u) ⬝ᵥ gram6 *ᵥ (M *ᵥ e) := by
          rw [Matrix.vecMul_transpose]

private lemma single_mulVec_entry (A : Mat6) (i j : Fin 6) :
    (Pi.single i (1 : ZMod 3)) ⬝ᵥ A *ᵥ (Pi.single j (1 : ZMod 3)) = A i j := by
  rw [single_one_dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]

private lemma col_eq (M : Mat6) (j i : Fin 6)
    (h : ∀ v : Vec6, bil6 (M.mulVec v) (M.mulVec (Pi.single j (1 : ZMod 3))) =
      bil6 v (Pi.single j (1 : ZMod 3))) :
    (Mᵀ * gram6 * M) i j = gram6 i j := by
  have hh := h (Pi.single i (1 : ZMod 3))
  rw [bil6, bil6] at hh
  have hL : (M *ᵥ Pi.single i (1 : ZMod 3)) ⬝ᵥ gram6 *ᵥ (M *ᵥ Pi.single j (1 : ZMod 3)) =
      (Mᵀ * gram6 * M) i j := by
    rw [← pullback_dot M (Pi.single i (1 : ZMod 3)) (Pi.single j (1 : ZMod 3))]
    exact single_mulVec_entry (Mᵀ * gram6 * M) i j
  have hR : (Pi.single i (1 : ZMod 3)) ⬝ᵥ gram6 *ᵥ Pi.single j (1 : ZMod 3) = gram6 i j :=
    single_mulVec_entry gram6 i j
  rw [hL, hR] at hh
  exact hh

theorem gram_block {M : Mat6} {c : ZMod 3} (hMy : M.mulVec (kY c) = 0)
    (h : ∀ i : Fin 5, ∀ v, bil6 (M.mulVec v) (M.mulVec (hJ i)) = bil6 v (hJ i)) :
    ∃ r : ZMod 3, Mᵀ * gram6 * M = gbetaR c r := by
  set G : Mat6 := Mᵀ * gram6 * M with hG
  have hGsymm : Gᵀ = G := by
    rw [hG, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      gram6_transpose, Matrix.mul_assoc]
  have hsymm : ∀ i j : Fin 6, G i j = G j i := by
    intro i j
    have hh := congr_fun (congr_fun hGsymm j) i
    simpa [Matrix.transpose_apply] using hh
  have hc0 : ∀ i : Fin 6, G i 0 = gram6 i 0 := by
    intro i
    have hh : ∀ v : Vec6,
        bil6 (M.mulVec v) (M.mulVec (Pi.single (0 : Fin 6) (1 : ZMod 3))) =
          bil6 v (Pi.single (0 : Fin 6) (1 : ZMod 3)) := by
      intro v
      rw [← hJ_zero]
      exact h 0 v
    simpa [hG] using col_eq M 0 i hh
  have hc1 : ∀ i : Fin 6, G i 1 = gram6 i 1 := by
    intro i
    have hh : ∀ v : Vec6,
        bil6 (M.mulVec v) (M.mulVec (Pi.single (1 : Fin 6) (1 : ZMod 3))) =
          bil6 v (Pi.single (1 : Fin 6) (1 : ZMod 3)) := by
      intro v
      rw [← hJ_one]
      exact h 1 v
    simpa [hG] using col_eq M 1 i hh
  have hc2 : ∀ i : Fin 6, G i 2 = gram6 i 2 := by
    intro i
    have hh : ∀ v : Vec6,
        bil6 (M.mulVec v) (M.mulVec (Pi.single (2 : Fin 6) (1 : ZMod 3))) =
          bil6 v (Pi.single (2 : Fin 6) (1 : ZMod 3)) := by
      intro v
      rw [← hJ_two]
      exact h 2 v
    simpa [hG] using col_eq M 2 i hh
  have hc3 : ∀ i : Fin 6, G i 3 = gram6 i 3 := by
    intro i
    have hh : ∀ v : Vec6,
        bil6 (M.mulVec v) (M.mulVec (Pi.single (3 : Fin 6) (1 : ZMod 3))) =
          bil6 v (Pi.single (3 : Fin 6) (1 : ZMod 3)) := by
      intro v
      rw [← hJ_three]
      exact h 3 v
    simpa [hG] using col_eq M 3 i hh
  have hr0 : ∀ j : Fin 6, G 0 j = gram6 0 j := by
    intro j
    rw [hsymm 0 j, hc0 j]
    exact gram6_symm j 0
  have hr1 : ∀ j : Fin 6, G 1 j = gram6 1 j := by
    intro j
    rw [hsymm 1 j, hc1 j]
    exact gram6_symm j 1
  have hr2 : ∀ j : Fin 6, G 2 j = gram6 2 j := by
    intro j
    rw [hsymm 2 j, hc2 j]
    exact gram6_symm j 2
  have hr3 : ∀ j : Fin 6, G 3 j = gram6 3 j := by
    intro j
    rw [hsymm 3 j, hc3 j]
    exact gram6_symm j 3
  have hG0 : G *ᵥ kY c = 0 := by
    rw [hG]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMy, Matrix.mulVec_zero,
      Matrix.mulVec_zero]
  have hker : ∀ i : Fin 6, G i 4 + c * G i 5 = 0 := by
    intro i
    have hi := congr_fun hG0 i
    rw [kY_single c, Matrix.mulVec_add, Matrix.mulVec_smul] at hi
    rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hi
    simp [Matrix.col_apply, smul_eq_mul] at hi
    exact hi
  have h54 : G 5 4 = -(G 5 5 * c) := by
    have hk := hker 5
    rw [eq_neg_of_add_eq_zero_left hk, mul_comm c (G 5 5)]
  have h45 : G 4 5 = -(G 5 5 * c) := by
    rw [hsymm 4 5, h54]
  have h44 : G 4 4 = G 5 5 * (c * c) := by
    have hk := hker 4
    rw [h45] at hk
    rw [eq_neg_of_add_eq_zero_left hk, mul_neg, neg_neg, ← mul_assoc c (G 5 5) c,
      mul_comm c (G 5 5), mul_assoc]
  refine ⟨G 5 5, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gbetaR, gram6, hc0, hc1, hc2, hc3, hr0, hr1, hr2, hr3, h44, h45, h54]

end E6Dep

end CFSG.StandardType

end
