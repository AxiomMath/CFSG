module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEvenDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalD4

open Module Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

section Herm

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem hermFourForm_hermU : hermFourForm D (hermU D) = 1 := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  apply (algebraMap K E).injective
  rw [algebraMap_hermFourForm, coe_hermU, map_one]
  exact det_swap_eq_one

theorem hermFourForm_hermI : hermFourForm D (hermI D) = 1 := by
  apply (algebraMap K E).injective
  rw [algebraMap_hermFourForm, coe_hermI, map_one, Matrix.det_one]

theorem algebraMap_polar_hermU (X : hermFourSpace D.σ) :
    algebraMap K E (polar (hermFourForm D) X (hermU D)) =
      (X : Matrix (Fin 2) (Fin 2) E) 0 1 + (X : Matrix (Fin 2) (Fin 2) E) 1 0 := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.polar, map_sub, map_sub, algebraMap_hermFourForm, algebraMap_hermFourForm,
    algebraMap_hermFourForm]
  simp only [Submodule.coe_add, coe_hermU, Matrix.det_fin_two, Matrix.add_apply]
  simp
  linear_combination (-((X : Matrix (Fin 2) (Fin 2) E) 0 1 +
    (X : Matrix (Fin 2) (Fin 2) E) 1 0)) * h2

theorem algebraMap_polar_hermI (X : hermFourSpace D.σ) :
    algebraMap K E (polar (hermFourForm D) X (hermI D)) =
      (X : Matrix (Fin 2) (Fin 2) E) 0 0 + (X : Matrix (Fin 2) (Fin 2) E) 1 1 := by
  rw [QuadraticMap.polar, map_sub, map_sub, algebraMap_hermFourForm, algebraMap_hermFourForm,
    algebraMap_hermFourForm]
  simp only [Submodule.coe_add, coe_hermI, Matrix.det_fin_two, Matrix.add_apply]
  simp
  ring

theorem polar_hermU_hermI : polar (hermFourForm D) (hermU D) (hermI D) = 0 := by
  apply (algebraMap K E).injective
  rw [algebraMap_polar_hermI, map_zero, coe_hermU]
  simp

theorem linearIndependent_hermU_hermI : LinearIndependent K ![hermU D, hermI D] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h := congrArg (fun X : hermFourSpace D.σ => (X : Matrix (Fin 2) (Fin 2) E)) hst
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp only [Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply, Matrix.smul_apply,
    coe_hermU, coe_hermI, Submodule.coe_zero, Matrix.zero_apply] at h00 h01
  simp [Algebra.smul_def] at h00 h01
  exact ⟨(algebraMap K E).injective (by rw [h01, map_zero]),
    (algebraMap K E).injective (by rw [h00, map_zero])⟩

theorem swap_mul_apply (Y : Matrix (Fin 2) (Fin 2) E) :
    (hermSwap D).1 * Y * ((hermSwap D).1.map D.σ)ᵀ = !![Y 1 1, Y 1 0; Y 0 1, Y 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermSwap, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.vecMul, dotProduct]

theorem hermFourRho_swap_apply (X : hermFourSpace D.σ) :
    hermFourRho D (hermSwap D) X = X + polar (hermFourForm D) X (hermU D) • hermU D +
      polar (hermFourForm D) X (hermI D) • hermI D := by
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hU := algebraMap_polar_hermU D X
  have hI := algebraMap_polar_hermI D X
  apply Subtype.ext
  ext i j
  rw [coe_hermFourRho, swap_mul_apply]
  simp only [Submodule.coe_add, Submodule.coe_smul, Matrix.add_apply, Matrix.smul_apply]
  simp only [Algebra.smul_def, hU, hI, coe_hermU, coe_hermI]
  fin_cases i <;> fin_cases j
  · simp
    linear_combination (-(X : Matrix (Fin 2) (Fin 2) E) 0 0) * h2
  · simp
    linear_combination (-(X : Matrix (Fin 2) (Fin 2) E) 0 1) * h2
  · simp
    linear_combination (-(X : Matrix (Fin 2) (Fin 2) E) 1 0) * h2
  · simp
    linear_combination (-(X : Matrix (Fin 2) (Fin 2) E) 1 1) * h2

end Herm

end CFSG.RankThree.PartOne.KCOrthogonalD4
