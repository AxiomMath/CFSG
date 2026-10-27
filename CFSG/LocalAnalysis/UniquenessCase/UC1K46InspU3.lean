module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K46InspL3
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UG
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open Matrix
open scoped MatrixGroups

namespace InspU3

section Isometry

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem conj_mem_SUid (hσ : ∀ c : K, σ (σ c) = c) {n : ℕ} {D A : GL (Fin n) K}
    (hD : conjTr σ (D : Matrix (Fin n) (Fin n) K) * (D : Matrix (Fin n) (Fin n) K) = 1)
    (hA : A ∈ SUid σ n) :
    D * A * D⁻¹ ∈ SUid σ n := by
  set Dm := (D : Matrix (Fin n) (Fin n) K)
  set Di := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set Am := (A : Matrix (Fin n) (Fin n) K)
  have hDDi : Dm * Di = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDi : Di = conjTr σ Dm := by
    calc Di = conjTr σ Dm * Dm * Di := by rw [hD, Matrix.one_mul]
      _ = conjTr σ Dm := by rw [Matrix.mul_assoc, hDDi, Matrix.mul_one]
  have hcc : conjTr σ (conjTr σ Dm) = Dm := by
    ext i j
    simp [conjTr, hσ]
  obtain ⟨hAdet, hAiso⟩ := mem_SUid.mp hA
  refine mem_SUid.mpr ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hAdet, mul_one, ← det_mul, hDDi, det_one]
  · rw [Units.val_mul, Units.val_mul]
    calc conjTr σ (Dm * Am * Di) * (Dm * Am * Di)
        = conjTr σ Di * conjTr σ Am * (conjTr σ Dm * Dm) * Am * Di := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = Dm * (conjTr σ Am * Am) * Di := by
          rw [hD, hDi, hcc]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hAiso, Matrix.mul_one, hDDi]

theorem normalizes_SUid (hσ : ∀ c : K, σ (σ c) = c) {n : ℕ} [Fintype K] {g : GL (Fin n) K}
    (hg : conjTr σ (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1) :
    (SUid σ n).map (MulAut.conj g).toMonoidHom = SUid σ n := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact conj_mem_SUid σ hσ hg hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Isometry

theorem cube_root_ne_zero {K : Type} [Field K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

section Unipotent

variable {K : Type} [Field K] [CharP K 2]

def vU (ω : K) : Fin 3 → K := ![1, ω, ω ^ 2]

def T (ω c : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + c • Matrix.vecMulVec (vU ω) (vU ω)

theorem cube_eq_one_of_root {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * hω

theorem vU_dot_vU {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (vU ω) ⬝ᵥ (vU ω) = 0 := by
  have h3 := cube_eq_one_of_root (K := K) hω
  simp only [vU, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination hω + ω * h3

theorem T_zero (ω : K) : T ω 0 = 1 := by
  simp [T]

theorem T_mul {ω a b : K} (hω : ω ^ 2 + ω + 1 = 0) :
    T ω a * T ω b = T ω (a + b) := by
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.vecMulVec (vU ω) (vU ω) with hM
  have hdot := vU_dot_vU (K := K) hω
  have hMM : M * M = 0 := by
    rw [hM, Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul]
    ext i j
    simp [Matrix.vecMulVec]
  have hkey : (a • M) * (b • M) = (a * b) • (M * M) := by
    rw [Matrix.smul_mul, Matrix.mul_smul]
    module
  simp only [T, ← hM]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hkey,
    hMM, smul_zero, add_zero, add_smul]
  simp only [one_mul, Matrix.one_mul]
  abel

theorem T_det {ω c : K} (hω : ω ^ 2 + ω + 1 = 0) : (T ω c).det = 1 := by
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.vecMulVec (vU ω) (vU ω) with hM
  have hdot := vU_dot_vU (K := K) hω
  have hMM : M * M = 0 := by
    rw [hM, Matrix.vecMulVec_mul_vecMulVec, hdot, zero_smul]
    ext i j
    simp [Matrix.vecMulVec]
  have hnil : IsNilpotent (c • M) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, hMM]
    simp
  have h := CFSG.LieType.BorelTits.det_one_add_of_isNilpotent (F := K) 2 hnil
  simpa only [T, ← hM] using h

theorem T_conjTr (σ : K ≃+* K) {ω c : K} (hσω : σ ω = ω) :
    conjTr σ (T ω c) = T ω (σ c) := by
  have hσω2 : σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, vU, conjTr, Matrix.map_apply, Matrix.vecMulVec, hσω, hσω2]
  all_goals exact Or.inl (mul_comm _ _)

theorem cycMat_mul_T {ω c : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (cycMat (F := K)) * T ω c * (cycMat (F := K))ᵀ = T ω (ω * c) := by
  have h3 := cube_eq_one_of_root (K := K) hω
  have h4 : ω ^ 4 = ω := by
    have h : ω ^ 4 = ω ^ 3 * ω := by ring
    rw [h, h3, one_mul]
  have hCv : (cycMat (F := K)) *ᵥ vU ω = ω ^ 2 • vU ω := by
    ext i
    fin_cases i <;> simp [cycMat, vU, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      ring_nf <;> simp [h3, h4]
  have hCvt : Matrix.vecMul (vU ω) ((cycMat (F := K))ᵀ) = ω ^ 2 • vU ω := by
    ext j
    fin_cases j <;> simp [cycMat, vU, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      ring_nf <;> simp [h3, h4]
  have hCC : (cycMat (F := K)) * (cycMat (F := K))ᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]
  have hquad : (cycMat (F := K)) * Matrix.vecMulVec (vU ω) (vU ω) *
      (cycMat (F := K))ᵀ = ω • Matrix.vecMulVec (vU ω) (vU ω) := by
    rw [Matrix.mul_vecMulVec, hCv, Matrix.vecMulVec_mul, hCvt]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [show ω ^ 2 * vU ω i * (ω ^ 2 * vU ω j) = ω ^ 4 * (vU ω i * vU ω j) by ring, h4]
  simp only [T]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hCC,
    hquad, smul_smul, mul_comm]

theorem T_mem_SUid (σ : K ≃+* K) {ω c : K} (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω)
    (hc : σ c = c) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero (T ω c) (by
      rw [T_det (K := K) hω]
      exact one_ne_zero)) ∈ SUid σ 3 := by
  rw [mem_SUid]
  change (T ω c).det = 1 ∧ conjTr σ (T ω c) * T ω c = 1
  refine ⟨T_det (K := K) hω, ?_⟩
  rw [T_conjTr σ hσω, T_mul (K := K) hω, hc]
  have hcc : c + c = 0 := CharTwo.add_self_eq_zero c
  rw [hcc]
  simp [T]

end Unipotent

section Standard

variable {K : Type} [Field K]

def cycSU (σ : K ≃+* K) : SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (cycMat (F := K)) (by
      rw [InspL3.cycMat_det]
      exact one_ne_zero), by
    rw [mem_SUid]
    change (cycMat (F := K)).det = 1 ∧
      conjTr σ (cycMat (F := K)) * cycMat (F := K) = 1
    refine ⟨InspL3.cycMat_det, ?_⟩
    have hmap : (cycMat (F := K)).map σ = cycMat (F := K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cycMat]
    rw [conjTr, hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]⟩

def xOddSU (σ : K ≃+* K) : SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0, 0; 0, -1, 0; 0, 0, -1] (by
      rw [Matrix.det_fin_three]; norm_num), by
    rw [mem_SUid]
    change (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      conjTr σ !![1, 0, 0; 0, -1, 0; 0, 0, -1] *
        !![1, 0, 0; 0, -1, 0; 0, 0, -1] = 1
    constructor
    · rw [Matrix.det_fin_three]; norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_three]⟩

def yOddSU (σ : K ≃+* K) : SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![-1, 0, 0; 0, -1, 0; 0, 0, 1] (by
      rw [Matrix.det_fin_three]; norm_num), by
    rw [mem_SUid]
    change (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      conjTr σ !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = 1
    constructor
    · rw [Matrix.det_fin_three]; norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_three]⟩

section Even

variable [CharP K 2]

def xEvenSU (σ : K ≃+* K) (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) : SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (T ω 1) (by
      rw [T_det (K := K) hω]; exact one_ne_zero),
    T_mem_SUid σ hω hσω (map_one σ)⟩

def yEvenSU (σ : K ≃+* K) (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) : SUid σ 3 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (T ω (ω ^ 2)) (by
      rw [T_det (K := K) hω]; exact one_ne_zero),
    T_mem_SUid σ hω hσω (by rw [map_pow, hσω])⟩

end Even

end Standard

section OddTriple

variable {K : Type} [Field K] (σ : K ≃+* K) (h2 : (2 : K) ≠ 0)

theorem xOddSU_mul_self : xOddSU σ * xOddSU σ = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, -1, 0; 0, 0, -1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem yOddSU_mul_self : yOddSU σ * yOddSU σ = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem xOddSU_mul_yOddSU_eq : xOddSU σ * yOddSU σ = yOddSU σ * xOddSU σ := by
  apply Subtype.ext
  apply Units.ext
  change (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
        !![1, 0, 0; 0, -1, 0; 0, 0, -1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem xOddSU_ne_one (h2 : (2 : K) ≠ 0) : xOddSU σ ≠ 1 := by
  intro h
  have h11 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 1) 1
  exact InspL3.neg_one_ne_one K h2 h11

theorem yOddSU_ne_one (h2 : (2 : K) ≠ 0) : yOddSU σ ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  exact InspL3.neg_one_ne_one K h2 h00

theorem xOddSU_ne_yOddSU (h2 : (2 : K) ≠ 0) : xOddSU σ ≠ yOddSU σ := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  exact InspL3.neg_one_ne_one K h2 h00.symm

theorem cycSU_mul_xOddSU :
    cycSU σ * xOddSU σ = (xOddSU σ * yOddSU σ) * cycSU σ := by
  apply Subtype.ext
  apply Units.ext
  change (cycMat (F := K)) * !![1, 0, 0; 0, -1, 0; 0, 0, -1] =
    ((!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1]) * cycMat (F := K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem cycSU_mul_yOddSU :
    cycSU σ * yOddSU σ = xOddSU σ * cycSU σ := by
  apply Subtype.ext
  apply Units.ext
  change (cycMat (F := K)) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
    (!![1, 0, 0; 0, -1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) * cycMat (F := K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem exists_inspPair_cycSUid_odd (h2 : (2 : K) ≠ 0) :
    ∃ S : Subgroup (SUid σ 3), InspPair 2 (Subgroup.zpowers (cycSU σ)) S := by
  have hdx : cycSU σ * xOddSU σ * (cycSU σ)⁻¹ = xOddSU σ * yOddSU σ := by
    rw [cycSU_mul_xOddSU]; group
  have hdy : cycSU σ * yOddSU σ * (cycSU σ)⁻¹ = xOddSU σ := by
    rw [cycSU_mul_yOddSU]; group
  obtain ⟨S, hEa, hcard, hnorm, hcomm⟩ :=
    exists_klein_of_triple (xOddSU_mul_self σ) (yOddSU_mul_self σ)
      (xOddSU_mul_yOddSU_eq σ) (xOddSU_ne_one σ h2) (yOddSU_ne_one σ h2)
      (xOddSU_ne_yOddSU σ h2) hdx hdy
  refine ⟨S, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hEa.1, ?_, hnorm, hcomm⟩
  intro hbot
  simp [hbot] at hcard

end OddTriple

section EvenTriple

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (ω : K)
  (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω)

theorem xEvenSU_mul_self : xEvenSU σ ω hω hσω * xEvenSU σ ω hω hσω = 1 := by
  apply Subtype.ext
  apply Units.ext
  change T ω 1 * T ω 1 = 1
  rw [T_mul (K := K) hω, CharTwo.add_self_eq_zero 1, T_zero]

theorem yEvenSU_mul_self : yEvenSU σ ω hω hσω * yEvenSU σ ω hω hσω = 1 := by
  apply Subtype.ext
  apply Units.ext
  change T ω (ω ^ 2) * T ω (ω ^ 2) = 1
  rw [T_mul (K := K) hω, CharTwo.add_self_eq_zero, T_zero]

theorem xEvenSU_mul_yEvenSU_eq :
    xEvenSU σ ω hω hσω * yEvenSU σ ω hω hσω =
      yEvenSU σ ω hω hσω * xEvenSU σ ω hω hσω := by
  apply Subtype.ext
  apply Units.ext
  change T ω 1 * T ω (ω ^ 2) = T ω (ω ^ 2) * T ω 1
  rw [T_mul (K := K) hω, T_mul (K := K) hω, add_comm]

theorem xEvenSU_ne_one : xEvenSU σ ω hω hσω ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (1 : K) + 1 = 1 := by
    simpa [xEvenSU, T, vU, Matrix.vecMulVec] using h00
  rw [CharTwo.add_self_eq_zero] at h00'
  exact zero_ne_one h00'

theorem yEvenSU_ne_one : yEvenSU σ ω hω hσω ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (1 : K) + ω ^ 2 = 1 := by
    simpa [yEvenSU, T, vU, Matrix.vecMulVec] using h00
  have hw2 : ω ^ 2 = 0 := add_left_cancel (a := (1 : K)) (by simpa using h00')
  exact pow_ne_zero 2 (cube_root_ne_zero hω) hw2

theorem xEvenSU_ne_yEvenSU : xEvenSU σ ω hω hσω ≠ yEvenSU σ ω hω hσω := by
  intro h
  have h00 := congrFun (congrFun (congrArg (fun z : SUid σ 3 =>
    ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h) 0) 0
  have h00' : (1 : K) + 1 = 1 + ω ^ 2 := by
    simpa [xEvenSU, yEvenSU, T, vU, Matrix.vecMulVec] using h00
  rw [CharTwo.add_self_eq_zero] at h00'
  have hw : ω = 0 := by linear_combination hω - h00'.symm
  exact cube_root_ne_zero hω hw

theorem cycMat_transpose_mul : (cycMat (F := K))ᵀ * cycMat (F := K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycSU_mul_xEvenSU :
    cycSU σ * xEvenSU σ ω hω hσω =
      (xEvenSU σ ω hω hσω * yEvenSU σ ω hω hσω) * cycSU σ := by
  apply Subtype.ext
  apply Units.ext
  have hZ : T ω 1 * T ω (ω ^ 2) = T ω ω := by
    rw [T_mul (K := K) hω]
    have h1 : (1 : K) + ω ^ 2 = ω := by
      linear_combination hω - CharTwo.add_self_eq_zero ω
    rw [h1]
  have hCX : (cycMat (F := K)) * T ω 1 = T ω ω * cycMat (F := K) := by
    calc (cycMat (F := K)) * T ω 1 =
        (cycMat (F := K)) * T ω 1 * ((cycMat (F := K))ᵀ * cycMat (F := K)) := by
          rw [cycMat_transpose_mul (K := K), Matrix.mul_one]
      _ = ((cycMat (F := K)) * T ω 1 * (cycMat (F := K))ᵀ) * cycMat (F := K) := by
          simp only [Matrix.mul_assoc]
      _ = T ω (ω * 1) * cycMat (F := K) := by
          rw [cycMat_mul_T (K := K) (ω := ω) (c := 1) hω]
      _ = T ω ω * cycMat (F := K) := by rw [mul_one]
  change (cycMat (F := K)) * T ω 1 = (T ω 1 * T ω (ω ^ 2)) * cycMat (F := K)
  rw [hZ]
  exact hCX

theorem cycSU_mul_yEvenSU :
    cycSU σ * yEvenSU σ ω hω hσω = xEvenSU σ ω hω hσω * cycSU σ := by
  apply Subtype.ext
  apply Units.ext
  have h3 : ω ^ 3 = 1 := cube_eq_one_of_root (K := K) hω
  have hCY : (cycMat (F := K)) * T ω (ω ^ 2) = T ω 1 * cycMat (F := K) := by
    calc (cycMat (F := K)) * T ω (ω ^ 2) =
        (cycMat (F := K)) * T ω (ω ^ 2) * ((cycMat (F := K))ᵀ * cycMat (F := K)) := by
          rw [cycMat_transpose_mul (K := K), Matrix.mul_one]
      _ = ((cycMat (F := K)) * T ω (ω ^ 2) * (cycMat (F := K))ᵀ) * cycMat (F := K) := by
          simp only [Matrix.mul_assoc]
      _ = T ω (ω * ω ^ 2) * cycMat (F := K) := by
          rw [cycMat_mul_T (K := K) (ω := ω) (c := ω ^ 2) hω]
      _ = T ω 1 * cycMat (F := K) := by
          rw [show ω * ω ^ 2 = 1 by rw [show ω * ω ^ 2 = ω ^ 3 by ring, h3]]
  change (cycMat (F := K)) * T ω (ω ^ 2) = T ω 1 * cycMat (F := K)
  exact hCY

end EvenTriple

theorem exists_inspPair_cycSUid_two {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (ω : K)
    (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) :
    ∃ S : Subgroup (SUid σ 3), InspPair 2 (Subgroup.zpowers (cycSU σ)) S := by
  have hdx : cycSU σ * xEvenSU σ ω hω hσω * (cycSU σ)⁻¹ =
      xEvenSU σ ω hω hσω * yEvenSU σ ω hω hσω := by
    rw [cycSU_mul_xEvenSU σ ω hω hσω]; group
  have hdy : cycSU σ * yEvenSU σ ω hω hσω * (cycSU σ)⁻¹ =
      xEvenSU σ ω hω hσω := by
    rw [cycSU_mul_yEvenSU σ ω hω hσω]; group
  obtain ⟨S, hEa, hcard, hnorm, hcomm⟩ :=
    exists_klein_of_triple (xEvenSU_mul_self σ ω hω hσω) (yEvenSU_mul_self σ ω hω hσω)
      (xEvenSU_mul_yEvenSU_eq σ ω hω hσω) (xEvenSU_ne_one σ ω hω hσω)
      (yEvenSU_ne_one σ ω hω hσω) (xEvenSU_ne_yEvenSU σ ω hω hσω) hdx hdy
  refine ⟨S, IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num), hEa.1, ?_, hnorm, hcomm⟩
  intro hbot
  simp [hbot] at hcard

section Conjugacy

variable {F : Type} [Field F]

theorem conjTr_mul_right_inv (σ : F ≃+* F) {B Bc Bi : Matrix (Fin 3) (Fin 3) F}
    (hB : conjTr σ B * B = antidiag 3) (hBc : conjTr σ Bc * Bc = antidiag 3)
    (hBiBc : conjTr σ Bi * conjTr σ Bc = 1) (hBcBi : Bc * Bi = 1) :
    conjTr σ (B * Bi) * (B * Bi) = 1 := by
  rw [conjTr_mul]
  calc conjTr σ Bi * conjTr σ B * (B * Bi)
      = conjTr σ Bi * (conjTr σ B * B) * Bi := by noncomm_ring
    _ = conjTr σ Bi * (conjTr σ Bc * Bc) * Bi := by rw [hB, hBc]
    _ = (conjTr σ Bi * conjTr σ Bc) * (Bc * Bi) := by noncomm_ring
    _ = 1 := by rw [hBiBc, hBcBi, Matrix.one_mul]

theorem exists_conj_SUid (σ : F ≃+* F) (hσσ : ∀ c : F, σ (σ c) = c) {ω : F}
    (h3 : (3 : F) ≠ 0) (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω)
    (hnorm : ∀ c : F, σ c = c → c ≠ 0 → ∃ β : F, σ β * β = c)
    (M : Matrix (Fin 3) (Fin 3) F) (hM3 : M * M * M = 1) (hMdet : M.det = 1)
    (hMiso : conjTr σ M * M = 1) (hMns : ∀ c : F, M ≠ c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ g : GL (Fin 3) F, conjTr σ (g : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      g * (cycSU σ : GL (Fin 3) F) * g⁻¹ =
        Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero) := by
  obtain ⟨B, hBdet, hBanti0, hMB⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm
    (1 : Matrix (Fin 3) (Fin 3) F) (conjTr_one σ) (by simp) M
    (by rw [Matrix.mul_one]; exact hMiso) hM3 hMdet hMns
  have hBanti : conjTr σ B * B = antidiag 3 := by simpa using hBanti0
  have hCiso : conjTr σ (cycMat (F := F)) * cycMat (F := F) = 1 :=
    (mem_SUid.mp (cycSU σ).2).2
  obtain ⟨Bc, hBcdet, hBcanti0, hCBc⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm
    (1 : Matrix (Fin 3) (Fin 3) F) (conjTr_one σ) (by simp) (cycMat (F := F))
    (by rw [Matrix.mul_one]; exact hCiso) InspL3.cycMat_cube InspL3.cycMat_det
    (fun c => InspL3.cycMat_ne_scalar c)
  have hBcanti : conjTr σ Bc * Bc = antidiag 3 := by simpa using hBcanti0
  let D : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![ω, 1, ω ^ 2]
  have hDdet : D.det ≠ 0 := by
    change (Matrix.diagonal ![ω, 1, ω ^ 2] : Matrix (Fin 3) (Fin 3) F).det ≠ 0
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      fin_cases i
      · simpa using cube_root_ne_zero hω
      · simp
      · simpa using pow_ne_zero 2 (cube_root_ne_zero hω)
  have hMB' : M * B = B * D := by simpa [D] using hMB
  have hCBc' : cycMat (F := F) * Bc = Bc * D := by simpa [D] using hCBc
  let Bg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  let Gg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Bc hBcdet
  let Dg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero D hDdet
  let Mg : GL (Fin 3) F := Matrix.GeneralLinearGroup.mkOfDetNeZero M
    (by rw [hMdet]; exact one_ne_zero)
  let g : GL (Fin 3) F := Bg * Gg⁻¹
  have hBcBi : Bc * ((Gg⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    change ((Gg : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((Gg⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hgiso : conjTr σ (g : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have hgval : (g : Matrix (Fin 3) (Fin 3) F) =
        B * ((Gg⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp [g, Bg, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
    rw [hgval]
    exact conjTr_mul_right_inv σ hBanti hBcanti
      (by rw [← conjTr_mul, hBcBi, conjTr_one]) hBcBi
  have hMBg : Mg * Bg = Bg * Dg := by
    apply Units.ext
    simpa [Mg, Bg, Dg, Matrix.GeneralLinearGroup.coe_mul] using hMB'
  have hCgG : (cycSU σ : GL (Fin 3) F) * Gg = Gg * Dg := by
    apply Units.ext
    change (cycMat (F := F)) * Bc = Bc * D
    exact hCBc'
  refine ⟨g, hgiso, ?_⟩
  have h1 : Gg⁻¹ * (cycSU σ : GL (Fin 3) F) * Gg = Dg := by
    calc Gg⁻¹ * (cycSU σ : GL (Fin 3) F) * Gg
        = Gg⁻¹ * ((cycSU σ : GL (Fin 3) F) * Gg) := by group
      _ = Gg⁻¹ * (Gg * Dg) := by rw [hCgG]
      _ = Dg := by group
  have h2 : Bg * Dg * Bg⁻¹ = Mg := by
    calc Bg * Dg * Bg⁻¹ = (Mg * Bg) * Bg⁻¹ := by rw [hMBg]
      _ = Mg := by group
  calc g * (cycSU σ : GL (Fin 3) F) * g⁻¹
      = Bg * (Gg⁻¹ * (cycSU σ : GL (Fin 3) F) * Gg) * Bg⁻¹ := by
        simp only [g]; group
    _ = Bg * Dg * Bg⁻¹ := by rw [h1]
    _ = Mg := h2

end Conjugacy

section CubeFacts

variable {K : Type} [Field K] [Fintype K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suid_cube_facts (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f)
    (hq : p ^ f % 3 = 1) {d : SUid σ 3} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      conjTr σ ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      ∀ c : K, ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
        c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨hdet, hiso⟩ := mem_SUid.mp d.2
  set M : Matrix (Fin 3) (Fin 3) K := ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hM
  have hcube : M * M * M = 1 := by
    have h1 : (d : GL (Fin 3) K) ^ 3 = 1 := by
      have := congrArg (fun x : SUid σ 3 => (x : GL (Fin 3) K)) hd3
      simpa using this
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [hM, pow_succ] using h2
  refine ⟨hcube, hdet, hiso, ?_⟩
  intro c hc
  have hc3 : c ^ 3 = 1 := by
    have h1 := hcube
    rw [hc] at h1
    have h2 := congrFun (congrFun h1 0) 0
    have h2' : c * (c * c) = 1 := by
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
    linear_combination h2'
  have hcQ : c ^ p ^ f = c := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 1 := ⟨(p ^ f) / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hc3, one_pow, one_mul]
  have hσc : σ c = c := by rw [hσ]; exact hcQ
  have hnorm : σ c * c = 1 := by
    have h4 := hiso
    rw [hc] at h4
    have e : conjTr σ (c • (1 : Matrix (Fin 3) (Fin 3) K)) =
        σ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [conjTr]
      · simp [conjTr, Matrix.one_apply, hij, Ne.symm hij]
    have e2 : (σ c • (1 : Matrix (Fin 3) (Fin 3) K)) *
        (c • (1 : Matrix (Fin 3) (Fin 3) K)) =
        (σ c * c) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    rw [e, e2] at h4
    have h6 := congrFun (congrFun h4 0) 0
    simpa using h6
  have hc1 : c = 1 := by
    have h7 : c * c = 1 := by rw [hσc] at hnorm; exact hnorm
    linear_combination hc3 - c * h7
  apply hd1
  apply Subtype.ext
  apply Units.ext
  show M = 1
  rw [hc, hc1, one_smul]

end CubeFacts

section Transfer

variable {K : Type} [Field K] [Fintype K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem inspPair_suid_of_std (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1)
    (hstd : ∃ S : Subgroup (SUid σ 3), InspPair 2 (Subgroup.zpowers (cycSU σ)) S)
    (D : Subgroup (SUid σ 3)) (hD : Nat.card D = 3) :
    ∃ U : Subgroup (SUid σ 3), InspPair 2 D U := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    subst h0
    have h2 : 2 ≤ p ^ 0 := two_le_of_card_eq_sq hK
    rw [pow_zero] at h2
    omega
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_pow_mod_one hf hq
  have hσσ : ∀ c : K, σ (σ c) = c := by
    intro c
    rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨ω, hω, hωQ⟩ := exists_cube_root (F := K) hK hq
  have hσω : σ ω = ω := by rw [hσ]; exact hωQ
  have hnorm : ∀ c : K, σ c = c → c ≠ 0 → ∃ β : K, σ β * β = c := by
    intro c hc hc0
    obtain ⟨β, hβ⟩ := exists_norm_eq hK (by rw [← hσ]; exact hc) hc0
    exact ⟨β, by rw [hσ]; exact hβ⟩
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  obtain ⟨hM3, hMdet, hMiso, hMns⟩ := suid_cube_facts σ hσ hq hd3 hd1
  obtain ⟨g, hgiso, hgconj⟩ := exists_conj_SUid σ hσσ h3 hω hσω hnorm
    ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) hM3 hMdet hMiso hMns
  have hg : (SUid σ 3).map (MulAut.conj g).toMonoidHom = SUid σ 3 :=
    normalizes_SUid σ hσσ hgiso
  obtain ⟨S, hS⟩ := hstd
  let φ : SUid σ 3 ≃* SUid σ 3 :=
    (Subgroup.equivMapOfInjective (SUid σ 3) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg)
  have hφC : φ (cycSU σ) = d := by
    apply Subtype.ext
    dsimp only [φ]
    simp only [MulEquiv.trans_apply, Subgroup.coe_equivMapOfInjective_apply,
      MulEquiv.subgroupCongr_apply]
    change g * (cycSU σ : GL (Fin 3) K) * g⁻¹ = (d : GL (Fin 3) K)
    rw [hgconj]
    exact Units.ext rfl
  have hφC' : φ.toMonoidHom (cycSU σ) = d := by simpa using hφC
  have hmap := hS.map φ
  rw [MonoidHom.map_zpowers, hφC', ← hDd] at hmap
  exact ⟨S.map φ.toMonoidHom, hmap⟩

end Transfer

end InspU3

theorem insp2L3_psu (G : Type) [Group G] [Finite G] (p f : ℕ) (hq : p ^ f % 3 = 1)
    (hL : LieModel G .PSU 3 p f) (D : Subgroup G) (hD : Nat.card D = 3) :
    ∃ U : Subgroup G, InspPair 2 D U := by
  have hadm := hL.admissible
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hp : p.Prime := hadm.1
    have hf : 1 ≤ f := hadm.2.1
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fintype K := Fintype.ofFinite K
    have hKc : CharP K p :=
      charP_of_card_eq_prime_pow (f := 2 * f)
        (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
    let e₁ : G ≃* CFSG.Open.StatedSU 3 (p ^ f) K :=
      (e.trans (QuotientGroup.quotientMulEquivOfEq
        (scalars_subgroupOf_statedSU_eq_bot hK hq))).trans QuotientGroup.quotientBot
    let e' : G ≃* SUid (unitaryInvolution K p f) 3 :=
      e₁.trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3).symm)
    have hstd : ∃ S : Subgroup (SUid (unitaryInvolution K p f) 3),
        InspPair 2 (Subgroup.zpowers (InspU3.cycSU (unitaryInvolution K p f))) S := by
      obtain ⟨ω, hω, hωQ⟩ := exists_cube_root (F := K) hK hq
      have hσω : unitaryInvolution K p f ω = ω := by
        rw [unitaryInvolution_apply]; exact hωQ
      by_cases hp2 : p = 2
      · subst hp2
        exact InspU3.exists_inspPair_cycSUid_two (unitaryInvolution K 2 f) ω hω hσω
      · exact InspU3.exists_inspPair_cycSUid_odd (unitaryInvolution K p f) (by
          intro h2
          have h2' : ((2 : ℕ) : K) = 0 := by simpa using h2
          have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2'
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd))
    obtain ⟨U', hpair⟩ := InspU3.inspPair_suid_of_std (unitaryInvolution K p f)
      (fun c => unitaryInvolution_apply K p f c) hK hq hstd (D.map e'.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e'.injective, hD])
    exact ⟨U'.map e'.symm.toMonoidHom, InspPair.of_map_equiv e' hpair⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem insp2L3_holds : Insp2L3 := by
  intro G _ _ hG D hD
  rcases hG with ⟨p, f, hq, hL⟩ | ⟨p, f, hq, hL⟩
  · exact insp2L3_psl G p f hq hL D hD
  · exact insp2L3_psu G p f hq hL D hD

end CFSG.LocalAnalysis.UniquenessCase.UCK