module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessMat
public import CFSG.RankThree.SubgroupLists.OrthogonalForms
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def hessS0Mat : Matrix (Fin 3) (Fin 3) K := fun i j => 2 / 3 - if i = j then 1 else 0

theorem hessSMat_zero (ω : K) : hessSMat ω 0 = hessS0Mat := by
  ext i j
  simp [hessSMat, hessS0Mat]

theorem hessS0Mat_mul_self (h3 : (3 : K) ≠ 0) : hessS0Mat (K := K) * hessS0Mat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessS0Mat, Matrix.one_apply] <;>
    field_simp <;>
    norm_num

@[expose] def hessS0 (h3 : (3 : K) ≠ 0) : GL (Fin 3) K :=
  ⟨hessS0Mat, hessS0Mat, hessS0Mat_mul_self h3, hessS0Mat_mul_self h3⟩

theorem coe_hessS0 (h3 : (3 : K) ≠ 0) :
    ((hessS0 h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessS0Mat :=
  rfl

theorem hessS0_eq (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : K) ≠ 0) :
    hessS0 h3 = hessPhi hω h3 * hessT 0 * (hessPhi hω h3)⁻¹ := by
  apply Units.ext
  rw [hessPhi_conj_hessT hω h3, hessSMat_zero, coe_hessS0]

@[expose] def hessNegTauMat : Matrix (Fin 3) (Fin 3) K := fun i j => if i + j = 0 then -1 else 0

theorem hessNegTauMat_mul_self : hessNegTauMat (K := K) * hessNegTauMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessNegTauMat, Matrix.one_apply]

@[expose] def hessNegTau : GL (Fin 3) K :=
  ⟨hessNegTauMat, hessNegTauMat, hessNegTauMat_mul_self, hessNegTauMat_mul_self⟩

@[expose] def hessRotMat (a b : K) : Matrix (Fin 3) (Fin 3) K := fun i j =>
  if i = 0 then (if j = 0 then 1 else 0) else if j = 0 then 0 else
    if i = j then a else if i = 1 then -b else b

theorem hessRotMat_mul (a b c d : K) :
    hessRotMat a b * hessRotMat c d = hessRotMat (a * c - b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessRotMat] <;>
    ring

theorem hessRotMat_one_zero : hessRotMat (1 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessRotMat, Matrix.one_apply]

@[expose] def hessRot {a b : K} (hab : a ^ 2 + b ^ 2 = 1) : GL (Fin 3) K :=
  ⟨hessRotMat a b, hessRotMat a (-b),
    by rw [hessRotMat_mul, ← hessRotMat_one_zero]; congr 1 <;> [linear_combination hab; ring],
    by rw [hessRotMat_mul, ← hessRotMat_one_zero]; congr 1 <;> [linear_combination hab; ring]⟩

theorem coe_hessRot {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    ((hessRot hab : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessRotMat a b :=
  rfl

theorem hessT_mem_soGL (i : Fin 3) : hessT i ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_soGL, coe_hessT, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [hessTMat, Matrix.diagonal_transpose, ← hessTMat, hessTMat_mul_self]
  · fin_cases i <;> simp [hessTMat, Matrix.det_diagonal, Fin.prod_univ_three]

theorem hessS0_mem_soGL (h3 : (3 : K) ≠ 0) : hessS0 h3 ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_soGL, coe_hessS0, Matrix.mul_one]
  have ht : (hessS0Mat (K := K))ᵀ = hessS0Mat := by
    ext i j
    simp only [Matrix.transpose_apply, hessS0Mat, eq_comm]
  refine ⟨by rw [ht, hessS0Mat_mul_self h3], ?_⟩
  rw [Matrix.det_fin_three]
  simp [hessS0Mat]
  field_simp
  norm_num

theorem hessC_mem_soGL : hessC ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_soGL, coe_hessC, Matrix.mul_one]
  refine ⟨hessCMat_transpose_mul, ?_⟩
  rw [Matrix.det_fin_three]
  simp [hessCMat]

theorem hessNegTau_mem_soGL : hessNegTau ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_soGL, Matrix.mul_one]
  have ht : (hessNegTauMat (K := K))ᵀ = hessNegTauMat := by
    ext i j
    simp only [Matrix.transpose_apply, hessNegTauMat, add_comm]
  refine ⟨by
    change (hessNegTauMat (K := K))ᵀ * hessNegTauMat = 1
    rw [ht, hessNegTauMat_mul_self], ?_⟩
  change (hessNegTauMat (K := K)).det = 1
  rw [Matrix.det_fin_three]
  simp [hessNegTauMat]

theorem hessRot_mem_soGL {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    hessRot hab ∈ soGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [mem_soGL, coe_hessRot, Matrix.mul_one]
  have ht : (hessRotMat a b)ᵀ = hessRotMat a (-b) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hessRotMat]
  refine ⟨by
    rw [ht, hessRotMat_mul, ← hessRotMat_one_zero]
    congr 1 <;> [linear_combination hab; ring], ?_⟩
  rw [Matrix.det_fin_three]
  simp [hessRotMat]
  linear_combination hab

theorem coe_hessC_inv :
    (((hessC : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessCMatᵀ :=
  rfl

theorem coe_hessT_inv (i : Fin 3) :
    (((hessT i : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessTMat i :=
  rfl

theorem coe_hessNegTau :
    ((hessNegTau : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessNegTauMat :=
  rfl

theorem coe_hessNegTau_inv :
    (((hessNegTau : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hessNegTauMat :=
  rfl

theorem coe_hessRot_inv {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    (((hessRot hab : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      hessRotMat a (-b) :=
  rfl

theorem hessC_commutator_hessT (i : Fin 3) :
    ⁅(hessC : GL (Fin 3) K), (hessT i : GL (Fin 3) K)⁆ = (hessT (i + 2) : GL (Fin 3) K) := by
  rw [commutatorElement_def, Units.ext_iff]
  simp only [Units.val_mul, coe_hessC, coe_hessT, coe_hessC_inv, coe_hessT_inv]
  ext j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessCMat, hessTMat, Matrix.diagonal]

theorem hessNegTau_commutator_hessC :
    ⁅(hessNegTau : GL (Fin 3) K), (hessC : GL (Fin 3) K)⁆ = (hessC : GL (Fin 3) K) := by
  rw [commutatorElement_def, Units.ext_iff]
  simp only [Units.val_mul, coe_hessC, coe_hessC_inv, coe_hessNegTau, coe_hessNegTau_inv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessCMat, hessNegTauMat]

theorem hessRot_commutator_hessT {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    ⁅hessRot hab, (hessT 1 : GL (Fin 3) K)⁆ = hessRot hab * hessRot hab := by
  rw [commutatorElement_def, Units.ext_iff]
  simp only [Units.val_mul, coe_hessRot, coe_hessT, coe_hessRot_inv, coe_hessT_inv]
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessRotMat, hessTMat, Matrix.diagonal] <;>
    ring

theorem hessT_mem_omegaGL (i : Fin 3) : hessT i ∈ omegaGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h := Subgroup.commutator_mem_commutator (hessC_mem_soGL (K := K)) (hessT_mem_soGL (i - 2))
  rwa [hessC_commutator_hessT, sub_add_cancel] at h

theorem hessC_mem_omegaGL : (hessC : GL (Fin 3) K) ∈ omegaGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h := Subgroup.commutator_mem_commutator (hessNegTau_mem_soGL (K := K)) hessC_mem_soGL
  rwa [hessNegTau_commutator_hessC] at h

theorem hessRot_sq_mem_omegaGL {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    hessRot hab * hessRot hab ∈ omegaGL (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h := Subgroup.commutator_mem_commutator (hessRot_mem_soGL hab) (hessT_mem_soGL (K := K) 1)
  rwa [hessRot_commutator_hessT] at h

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
