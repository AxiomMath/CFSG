module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K]

@[expose] def sMat (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, M 0 0, M 0 1, 0; 0, M 1 0, M 1 1, 0; 0, 0, 0, 1]

theorem sMat_mul (M N : Matrix (Fin 2) (Fin 2) K) : sMat M * sMat N = sMat (M * N) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem sMat_one : sMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat]

@[expose] def dMat (l : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  !![(l : K), 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, ((l⁻¹ : Kˣ) : K)]

theorem dMat_mul (l m : Kˣ) : dMat l * dMat m = dMat (l * m) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dMat, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

theorem dMat_one : dMat (1 : Kˣ) = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dMat]

theorem dMat_mem (l : Kˣ) : (dMat l)ᵀ * minorJ K * dMat l = minorJ K := by
  ext k j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases j <;> simp [dMat]

abbrev mat (g : antiSp K) : Matrix (Fin 4) (Fin 4) K := glMat (g : GL (Fin 4) K)

theorem mat_mul (g h : antiSp K) : mat (g * h) = mat g * mat h :=
  rfl

theorem mat_one : mat (1 : antiSp K) = 1 :=
  rfl

theorem mat_ext {g h : antiSp K} (H : mat g = mat h) : g = h :=
  antiSp_ext H

variable [CharP K 2]

theorem sMat_mem {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1) :
    (sMat M)ᵀ * minorJ K * sMat M = minorJ K := by
  rw [Matrix.det_fin_two] at hM
  ext k l
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases l <;> simp [sMat] <;> grind

@[expose] def sElt (M : SL₂ K) : antiSp K :=
  ⟨⟨sMat (M : Matrix (Fin 2) (Fin 2) K), sMat ((M⁻¹ : SL₂ K) : Matrix (Fin 2) (Fin 2) K),
    by rw [sMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, sMat_one],
    by rw [sMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, sMat_one]⟩, sMat_mem M.2⟩

theorem mat_sElt (M : SL₂ K) : mat (sElt M) = sMat (M : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem glMat_sElt (M : SL₂ K) :
    glMat (sElt M : GL (Fin 4) K) = sMat (M : Matrix (Fin 2) (Fin 2) K) :=
  rfl

variable (K) in
@[expose] def sHom₂ : SL₂ K →* antiSp K where
  toFun := sElt
  map_one' := mat_ext (by
    rw [mat_sElt, Matrix.SpecialLinearGroup.coe_one, sMat_one, mat_one])
  map_mul' M N := mat_ext (by
    rw [mat_mul, mat_sElt, mat_sElt, mat_sElt, Matrix.SpecialLinearGroup.coe_mul, sMat_mul])

theorem sHom₂_apply (M : SL₂ K) : sHom₂ K M = sElt M :=
  rfl

theorem sHom₂_injective : Function.Injective (sHom₂ K) := by
  intro M N h
  have h1 := congrArg mat h
  simp only [sHom₂_apply, mat_sElt] at h1
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [sMat] using congrFun (congrFun h1 1) 1
  · simpa [sMat] using congrFun (congrFun h1 1) 2
  · simpa [sMat] using congrFun (congrFun h1 2) 1
  · simpa [sMat] using congrFun (congrFun h1 2) 2

@[expose] def dElt (l : Kˣ) : antiSp K :=
  ⟨⟨dMat l, dMat l⁻¹, by rw [dMat_mul, mul_inv_cancel, dMat_one],
    by rw [dMat_mul, inv_mul_cancel, dMat_one]⟩, dMat_mem l⟩

omit [CharP K 2] in
theorem mat_dElt (l : Kˣ) : mat (dElt l) = dMat l :=
  rfl

omit [CharP K 2] in
theorem glMat_dElt (l : Kˣ) : glMat (dElt l : GL (Fin 4) K) = dMat l :=
  rfl

variable (K) in
@[expose] def dHom₂ : Kˣ →* antiSp K where
  toFun := dElt
  map_one' := mat_ext (by rw [mat_dElt, dMat_one, mat_one])
  map_mul' l m := mat_ext (by rw [mat_mul, mat_dElt, mat_dElt, mat_dElt, dMat_mul])

omit [CharP K 2] in
theorem dHom₂_apply (l : Kˣ) : dHom₂ K l = dElt l :=
  rfl

omit [CharP K 2] in
theorem dHom₂_injective : Function.Injective (dHom₂ K) := by
  intro l m h
  have h1 := congrArg mat h
  simp only [dHom₂_apply, mat_dElt] at h1
  exact Units.ext (by simpa [dMat] using congrFun (congrFun h1 0) 0)

theorem sElt_mul_dElt (M : SL₂ K) (l : Kˣ) : sElt M * dElt l = dElt l * sElt M :=
  mat_ext (by
    rw [mat_mul, mat_mul, mat_sElt, mat_dElt]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sMat, dMat, Matrix.mul_apply, Fin.sum_univ_four])

@[expose] def aElt (v : Fin 2 → K) (c : K) : antiSp K := uElt (v 1) (v 0) c 0

theorem aElt_mul (v w : Fin 2 → K) (c e : K) :
    aElt v c * aElt w e = aElt (v + w) (c + e + (v 0 * w 1 + v 1 * w 0)) := by
  rw [aElt, aElt, aElt, uElt_mul]
  have e1 : (v + w) 1 = v 1 + w 1 := rfl
  have e0 : (v + w) 0 = v 0 + w 0 := rfl
  rw [e1, e0]
  congr 1 <;> ring

theorem aElt_zero_zero : aElt (0 : Fin 2 → K) 0 = 1 := by
  rw [aElt]
  simpa using uElt_zero_eq_one (K := K)

theorem aElt_mul_self (v : Fin 2 → K) (c : K) : aElt v c * aElt v c = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [aElt_mul, ← aElt_zero_zero]
  congr 1
  · ext i
    simp [CharTwo.add_self_eq_zero]
  · linear_combination (c + v 0 * v 1) * h2

theorem aElt_inv (v : Fin 2 → K) (c : K) : (aElt v c)⁻¹ = aElt v c :=
  inv_eq_of_mul_eq_one_right (aElt_mul_self v c)

theorem mat_aElt (v : Fin 2 → K) (c : K) : mat (aElt v c) = uMat (v 1) (v 0) c 0 :=
  rfl

theorem glMat_aElt (v : Fin 2 → K) (c : K) :
    glMat (aElt v c : GL (Fin 4) K) = uMat (v 1) (v 0) c 0 :=
  rfl

theorem dElt_mul_aElt (l : Kˣ) (v : Fin 2 → K) (c : K) :
    dElt l * aElt v c = aElt ((l : K) • v) ((l : K) ^ 2 * c) * dElt l :=
  mat_ext (by
    rw [mat_mul, mat_mul, mat_dElt, mat_aElt, mat_aElt]
    have hl : (l : K) * ((l⁻¹ : Kˣ) : K) = 1 := Units.mul_inv l
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dMat, uMat, Matrix.mul_apply, Fin.sum_univ_four] <;> grind)

theorem sElt_mul_aElt (M : SL₂ K) (v : Fin 2 → K) (c : K) :
    sElt M * aElt v c = aElt ((M : Matrix (Fin 2) (Fin 2) K) *ᵥ v) c * sElt M :=
  mat_ext (by
    rw [mat_mul, mat_mul, mat_sElt, mat_aElt, mat_aElt]
    have hdet := M.det_coe
    rw [Matrix.det_fin_two] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sMat, uMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;> grind)

end KCRootAxis

end CFSG.RankThree.PartOne
