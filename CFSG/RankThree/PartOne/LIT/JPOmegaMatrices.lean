module

public import CFSG.RankThree.PartOne.LIT.CongruenceSplit
public import CFSG.RankThree.SubgroupLists.OrthogonalForms

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def splitFormK (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 2, 0; 1, 0, 0]

theorem splitForm_eq (p : ℕ) [Fact p.Prime] : splitForm p = splitFormK (ZMod p) := rfl

@[expose] def adU (s : K) : Matrix (Fin 3) (Fin 3) K := !![1, -2 * s, -s ^ 2; 0, 1, s; 0, 0, 1]

@[expose] def adD (σ : K) : Matrix (Fin 3) (Fin 3) K := !![σ, 0, 0; 0, 1, 0; 0, 0, σ⁻¹]

@[expose] def adN : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem adU_add (s r : K) : adU s * adU r = adU (s + r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adU, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem adU_zero : adU (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adU]

theorem det_adU (s : K) : (adU s).det = 1 := by
  simp [adU, Matrix.det_fin_three]

theorem det_adD {σ : K} (h : σ ≠ 0) : (adD σ).det = 1 := by
  simp [adD, Matrix.det_fin_three, h]

theorem det_adN : (adN : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [adN, Matrix.det_fin_three]

theorem adU_orth (s : K) : (adU s)ᵀ * splitFormK K * adU s = splitFormK K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adU, splitFormK, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem adD_orth {σ : K} (h : σ ≠ 0) : (adD σ)ᵀ * splitFormK K * adD σ = splitFormK K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adD, splitFormK, Matrix.mul_apply, Fin.sum_univ_three, h]

theorem adN_orth : (adN : Matrix (Fin 3) (Fin 3) K)ᵀ * splitFormK K * adN = splitFormK K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adN, splitFormK, Matrix.mul_apply, Fin.sum_univ_three]

theorem adD_mul_adU {σ : K} (h : σ ≠ 0) (s : K) : adD σ * adU s = adU (σ * s) * adD σ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adD, adU, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp

theorem adD_mul (σ τ : K) : adD σ * adD τ = adD (σ * τ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adD, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem adD_one : adD (1 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adD]

theorem adN_mul_adD (σ : K) : adN * adD σ = adD σ⁻¹ * adN := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adN, adD, Matrix.mul_apply, Fin.sum_univ_three]

theorem adN_mul_adN : (adN : Matrix (Fin 3) (Fin 3) K) * adN = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adN, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def uGL (s : K) : GL (Fin 3) K :=
  ⟨adU s, adU (-s), by rw [adU_add, add_neg_cancel, adU_zero],
    by rw [adU_add, neg_add_cancel, adU_zero]⟩

@[expose] def dGL (σ : K) (_ : σ ≠ 0) : GL (Fin 3) K :=
  ⟨adD σ, adD σ⁻¹, by rw [adD_mul, mul_inv_cancel₀ (by assumption), adD_one],
    by rw [adD_mul, inv_mul_cancel₀ (by assumption), adD_one]⟩

@[expose] def nGL : GL (Fin 3) K := ⟨adN, adN, adN_mul_adN, adN_mul_adN⟩

theorem uGL_mem_so (s : K) : uGL s ∈ soGL (splitFormK K) :=
  mem_soGL.mpr ⟨adU_orth s, det_adU s⟩

theorem dGL_mem_so {σ : K} (h : σ ≠ 0) : dGL σ h ∈ soGL (splitFormK K) :=
  mem_soGL.mpr ⟨adD_orth h, det_adD h⟩

theorem nGL_mem_so : (nGL : GL (Fin 3) K) ∈ soGL (splitFormK K) :=
  mem_soGL.mpr ⟨adN_orth, det_adN⟩

theorem dGL_congr {σ τ : K} (h : σ = τ) (hσ : σ ≠ 0) (hτ : τ ≠ 0) : dGL σ hσ = dGL τ hτ := by
  subst h
  rfl

theorem uGL_comm (h2 : (2 : K) ≠ 0) (s : K) : ⁅dGL 2 h2, uGL s⁆ = uGL s := by
  apply Units.ext
  rw [commutatorElement_def]
  show adD 2 * adU s * adD 2⁻¹ * adU (-s) = adU s
  rw [adD_mul_adU h2, Matrix.mul_assoc (adU (2 * s)), adD_mul, mul_inv_cancel₀ h2, adD_one,
    Matrix.mul_one, adU_add]
  congr 1
  ring

theorem nGL_comm {σ : K} (h : σ ≠ 0) :
    ⁅(nGL : GL (Fin 3) K), dGL σ h⁆ =
      dGL (σ⁻¹ * σ⁻¹) (mul_ne_zero (inv_ne_zero h) (inv_ne_zero h)) := by
  apply Units.ext
  rw [commutatorElement_def]
  show adN * adD σ * adN * adD σ⁻¹ = adD (σ⁻¹ * σ⁻¹)
  rw [adN_mul_adD, Matrix.mul_assoc (adD σ⁻¹), adN_mul_adN, Matrix.mul_one, adD_mul]

theorem uGL_mem_omega (h2 : (2 : K) ≠ 0) (s : K) : uGL s ∈ omegaGL (splitFormK K) := by
  rw [← uGL_comm h2 s]
  exact Subgroup.commutator_mem_commutator (dGL_mem_so h2) (uGL_mem_so s)

theorem four_ne_zero' (h2 : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have : (4 : K) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem dGL_four_mem_omega (h2 : (2 : K) ≠ 0) :
    dGL 4 (four_ne_zero' h2) ∈ omegaGL (splitFormK K) := by
  have h : (2 : K)⁻¹ ≠ 0 := inv_ne_zero h2
  have e : ((2 : K)⁻¹)⁻¹ * ((2 : K)⁻¹)⁻¹ = 4 := by norm_num
  have := Subgroup.commutator_mem_commutator (nGL_mem_so (K := K)) (dGL_mem_so h)
  rw [nGL_comm h, dGL_congr e _ (four_ne_zero' h2)] at this
  exact this

end CFSG.RankThree.PartOne.LIT
