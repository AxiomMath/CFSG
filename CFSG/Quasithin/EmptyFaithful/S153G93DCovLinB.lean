module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinA

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovLin

open scoped LinearAlgebra.Projectivization Matrix
open CFSG.Assembly.LowTwoRank

section Elements

variable {K : Type} [Field K]

theorem sl3_det_diagR [CharP K 2] :
    (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Matrix.det_fin_three]
  simp
  linear_combination (-1 : K) * h2

theorem sl3_diagR_cube [CharP K 2] :
    (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) *
      (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) *
      (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination h2

theorem exists_sl3_order_three_fixing_basis [CharP K 2] :
    ∃ D : Matrix.SpecialLinearGroup (Fin 3) K, D ^ 3 = 1 ∧ D ≠ 1 ∧
      (D : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1 : Fin 3 → K) = Pi.single 0 1 := by
  let D : Matrix.SpecialLinearGroup (Fin 3) K := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], sl3_det_diagR⟩
  have hD : (D : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, 1, 1] := rfl
  refine ⟨D, ?_, ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, hD, pow_three']
    exact sl3_diagR_cube
  · intro h
    have h11 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K) 1 1) h
    simp [hD] at h11
  · rw [hD]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Elements

theorem exists_sl3_mulVec_eq_smul {K : Type} [Field K] {e v : Fin 3 → K} (he : e ≠ 0)
    (hv : v ≠ 0) : ∃ (g : Matrix.SpecialLinearGroup (Fin 3) K) (c : Kˣ),
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = (c : K) • v := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) K)
    (Projectivization.mk K e he) (Projectivization.mk K v hv)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  exact ⟨g, c, hc.symm⟩

theorem exists_sl3_order_three_fixing {K : Type} [Field K] [CharP K 2] {v : Fin 3 → K}
    (hv : v ≠ 0) : ∃ γ ∈ StatedSL 3 K, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
      ((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  obtain ⟨D, hD3, hD1, hDe⟩ := exists_sl3_order_three_fixing_basis (K := K)
  have he : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := fun h => by
    simpa using congrFun h 0
  obtain ⟨g, c, hgc⟩ := exists_sl3_mulVec_eq_smul he hv
  have hmem : ∀ x : Matrix.SpecialLinearGroup (Fin 3) K,
      Matrix.SpecialLinearGroup.toGL x ∈ StatedSL 3 K := fun x => by
    rw [statedSL_eq_range_toGL]
    exact ⟨x, rfl⟩
  refine exists_order_three_fixing_of_conj c.ne_zero (hmem D) (hmem g) ?_ ?_ hDe hgc
  · rw [← map_pow, hD3, map_one]
  · intro h
    exact hD1 (Matrix.SpecialLinearGroup.toGL_injective (by rw [h, map_one]))

end CovLin

end S153G93D

end CFSG.Quasithin
