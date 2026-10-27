module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open Matrix

section Ring

variable {R : Type*} [CommRing R]

@[expose] def companion3 (a b c : R) : Matrix (Fin 3) (Fin 3) R := !![0, 0, a; 1, 0, b; 0, 1, c]

@[expose] def hankel3 (b c : R) : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, c; 1, c, b + c * c]

@[expose] def swap12 : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def swap23 : Matrix (Fin 3) (Fin 3) R := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

@[expose] def tau3 (b c : R) : Matrix (Fin 3) (Fin 3) R := !![1, 0, b; 0, 1, c; 0, 0, 1]

theorem hankel3_transpose (b c : R) : (hankel3 b c)ᵀ = hankel3 b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hankel3]

theorem hankel3_mul_companion3 (a b c : R) :
    hankel3 b c * companion3 a b c = (companion3 a b c)ᵀ * hankel3 b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hankel3, companion3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_companion3 (a b c : R) : (companion3 a b c).det = a := by
  rw [Matrix.det_fin_three]
  simp [companion3]

theorem det_hankel3_mul_self (b c : R) : (hankel3 b c).det * (hankel3 b c).det = 1 := by
  have h : (hankel3 b c).det = -1 := by
    rw [Matrix.det_fin_three]
    simp [hankel3]
  rw [h]
  norm_num

theorem companion3_one_eq [CharP R 2] (b c : R) :
    companion3 1 b c = swap12 * swap23 * tau3 b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion3, swap12, swap23, tau3, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mul_self : (swap12 : Matrix (Fin 3) (Fin 3) R) * swap12 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap12, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem swap23_mul_self : (swap23 : Matrix (Fin 3) (Fin 3) R) * swap23 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap23, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem tau3_mul_self [CharP R 2] (b c : R) : tau3 b c * tau3 b c = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tau3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

theorem det_swap12 [CharP R 2] : (swap12 : Matrix (Fin 3) (Fin 3) R).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [swap12, CharTwo.neg_eq]

theorem det_swap23 [CharP R 2] : (swap23 : Matrix (Fin 3) (Fin 3) R).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [swap23, CharTwo.neg_eq]

theorem det_tau3 (b c : R) : (tau3 b c).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [tau3]

theorem swap12_ne_one [Nontrivial R] : (swap12 : Matrix (Fin 3) (Fin 3) R) ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [swap12, Matrix.one_apply] at h01

theorem swap23_ne_one [Nontrivial R] : (swap23 : Matrix (Fin 3) (Fin 3) R) ≠ 1 := by
  intro h
  have h12 := congrFun (congrFun h 1) 2
  simp [swap23, Matrix.one_apply] at h12

theorem tau3_ne_one {b c : R} (h : b ≠ 0 ∨ c ≠ 0) : tau3 b c ≠ 1 := by
  intro h1
  rcases h with hb | hc
  · exact hb (by simpa [tau3, Matrix.one_apply] using congrFun (congrFun h1 0) 2)
  · exact hc (by simpa [tau3, Matrix.one_apply] using congrFun (congrFun h1 1) 2)

end Ring

section Field

variable {F : Type*} [Field F]

theorem exists_conj_companion3 (y : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F)
    (hv : LinearIndependent F ![v, y *ᵥ v, y *ᵥ (y *ᵥ v)]) :
    ∃ (P : GL (Fin 3) F) (a b c : F),
      y = (P : Matrix (Fin 3) (Fin 3) F) * companion3 a b c *
        ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have hunit : IsUnit (Matrix.of fun (i j : Fin 3) => ![v, y *ᵥ v, y *ᵥ (y *ᵥ v)] j i) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hv
  obtain ⟨P, hP⟩ := hunit
  have hPij : ∀ i j, (P : Matrix (Fin 3) (Fin 3) F) i j = ![v, y *ᵥ v, y *ᵥ (y *ᵥ v)] j i :=
    fun i j => congrFun (congrFun hP i) j
  obtain ⟨z, hz⟩ : ∃ z : Fin 3 → F,
      (P : Matrix (Fin 3) (Fin 3) F) *ᵥ z = y *ᵥ (y *ᵥ (y *ᵥ v)) :=
    ⟨((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (y *ᵥ (y *ᵥ (y *ᵥ v))), by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have key : y * (P : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) * companion3 (z 0) (z 1) (z 2) := by
    ext i j
    have h := congrFun hz i
    fin_cases j
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, companion3, hPij]
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, companion3, hPij]
      ring
    · simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, companion3, hPij]
        at h ⊢
      linear_combination (-1 : F) * h
  refine ⟨P, z 0, z 1, z 2, ?_⟩
  have h1 : y * (P : Matrix (Fin 3) (Fin 3) F) * ((P⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = y := by
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← h1, key]

end Field

end CFSG.RankThree.PartTwo.Sec3.Sims321
