module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero

public section

namespace CFSG.FiniteField

open Matrix

theorem exists_mem_ne_zero_dotProduct_mulVec_eq_zero {K : Type*} [Field K] [Finite K]
    {ι : Type*} [Fintype ι] (U : Submodule K (ι → K)) (hU : 3 ≤ Module.finrank K U)
    (M : Matrix ι ι K) : ∃ u ∈ U, u ≠ 0 ∧ u ⬝ᵥ (M *ᵥ u) = 0 := by
  classical
  set m := Module.finrank K U
  let b : Module.Basis (Fin m) K U := Module.finBasis K U
  let M' : Matrix (Fin m) (Fin m) K := fun i j => (b i : ι → K) ⬝ᵥ (M *ᵥ (b j : ι → K))
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_dotProduct_mulVec_eq_zero
    (by rwa [Fintype.card_fin]) M'
  set x : U := b.equivFun.symm c
  have hx : (x : ι → K) = ∑ i, c i • (b i : ι → K) := by
    simp [x, Module.Basis.equivFun_symm_apply]
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h0
    apply hc0
    have hx0 : x = 0 := Subtype.ext h0
    rw [← b.equivFun.apply_symm_apply c, show b.equivFun.symm c = x from rfl, hx0, map_zero]
  · rw [hx]
    have hlhs : (∑ i, c i • (b i : ι → K)) ⬝ᵥ (M *ᵥ ∑ j, c j • (b j : ι → K)) =
        ∑ i, ∑ j, c i * c j * M' i j := by
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, M', Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hlhs]
    rw [← hc]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

end CFSG.FiniteField
