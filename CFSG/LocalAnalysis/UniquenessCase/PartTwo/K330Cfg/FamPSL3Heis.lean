module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.AutBigKit
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open Matrix
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

section Matrices

variable {K : Type} [Field K]

private def k330c_mA (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal (fun i => ω ^ (i : ℕ))

private def k330c_mB : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of (fun i j : Fin 3 => if i = j + 1 then (1 : K) else 0)

private def k330c_mF (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of (fun i j : Fin 3 => ω ^ ((i : ℕ) * (j : ℕ)))

private def k330c_mT (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal (fun i => if i = (2 : Fin 3) then ω else 1)

private lemma k330c_om4 {ω : K} (h3 : ω ^ 3 = 1) : ω ^ 4 = ω := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]

private lemma k330c_om5 {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    ω ^ 5 = -1 - ω := by
  rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, h3, one_mul, h2]

private lemma k330c_om6 {ω : K} (h3 : ω ^ 3 = 1) : ω ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, h3, mul_one]

private lemma k330c_om7 {ω : K} (h3 : ω ^ 3 = 1) : ω ^ 7 = ω := by
  rw [show (7 : ℕ) = 3 + 4 by norm_num, pow_add, h3, one_mul, k330c_om4 h3]

private lemma k330c_om8 {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    ω ^ 8 = -1 - ω := by
  rw [show (8 : ℕ) = 3 + 5 by norm_num, pow_add, h3, one_mul, k330c_om5 h2 h3]

private lemma k330c_om9 {ω : K} (h3 : ω ^ 3 = 1) : ω ^ 9 = 1 := by
  rw [show (9 : ℕ) = 3 + 6 by norm_num, pow_add, h3, one_mul, k330c_om6 h3]

private lemma k330c_om12 {ω : K} (h3 : ω ^ 3 = 1) : ω ^ 12 = 1 := by
  rw [show (12 : ℕ) = 6 + 6 by norm_num, pow_add, k330c_om6 h3, mul_one]

private lemma k330c_omega_pow_cube {ω : K} (h3 : ω ^ 3 = 1) (n : ℕ) : (ω ^ n) ^ 3 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, h3, one_pow]

private lemma k330c_mA_cube {ω : K} (h3 : ω ^ 3 = 1) : k330c_mA ω ^ 3 = 1 := by
  rw [k330c_mA, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Pi.pow_apply, h3, k330c_omega_pow_cube h3]

private lemma k330c_mB_cube : k330c_mB ^ 3 = (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [pow_succ, pow_succ, pow_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private lemma k330c_mA_mB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    k330c_mA ω * k330c_mB = ω • (k330c_mB * k330c_mA ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mB, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring_nf <;>
    simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
      k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero] <;>
    ring

private lemma k330c_mF_mA {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    k330c_mF ω * k330c_mA ω = k330c_mBᵀ * k330c_mF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mB, k330c_mF, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    ring_nf <;>
    simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
      k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero] <;>
    ring

private lemma k330c_mF_mB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    k330c_mF ω * k330c_mB = k330c_mA ω * k330c_mF ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mB, k330c_mF, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    ring_nf <;>
    simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
      k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero] <;>
    ring

private lemma k330c_mB_mul_transpose : k330c_mB * k330c_mBᵀ =
    (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

private lemma k330c_mB_inv : (k330c_mB : Matrix (Fin 3) (Fin 3) K)⁻¹ = k330c_mBᵀ :=
  Matrix.inv_eq_right_inv k330c_mB_mul_transpose

private lemma k330c_det_mA {ω : K} (h3 : ω ^ 3 = 1) : (k330c_mA ω).det = 1 := by
  rw [k330c_mA, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_mul]
  rw [show ω * ω ^ 2 = 1 by rw [← pow_succ' ω 2, h3]]

private lemma k330c_det_mB : (k330c_mB : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [k330c_mB]

private lemma k330c_det_mF {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    (k330c_mF ω).det = (1 - ω) ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [k330c_mF]
  ring_nf
  simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
    k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero]
  ring

private lemma k330c_det_mT {ω : K} : (k330c_mT ω).det = ω := by
  rw [k330c_mT, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

private lemma k330c_mT_mA {ω : K} :
    k330c_mT ω * k330c_mA ω = k330c_mA ω * k330c_mT ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mT, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

private lemma k330c_mT_mB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    k330c_mT ω * k330c_mB = k330c_mB * k330c_mA ω * k330c_mT ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mB, k330c_mT, Matrix.diagonal_apply, Matrix.mul_apply,
      Fin.sum_univ_three] <;>
    ring_nf <;>
    simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
      k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero] <;>
    ring

private lemma k330c_mA_not_scalar {ω : K} (hω1 : ω ≠ 1) {c : K} :
    k330c_mA ω ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [k330c_mA, Matrix.diagonal_apply] at h00 h11
  exact hω1 (h11.trans h00.symm)

private lemma k330c_mB_not_scalar {c : K} :
    k330c_mB ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp [k330c_mB, Matrix.one_apply] at h02

private lemma k330c_mA_mB_not_scalar {ω : K} (hω0 : ω ≠ 0) {c : K} :
    k330c_mA ω * k330c_mB ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  simp [k330c_mA, k330c_mB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h10
  exact hω0 h10

private lemma k330c_mA_mBtranspose_not_scalar {ω : K} {c : K} :
    k330c_mA ω * k330c_mBᵀ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [k330c_mA, k330c_mB, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h01

private lemma k330c_mA_mB_mA {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1) :
    k330c_mA ω * k330c_mB * k330c_mA ω =
      (k330c_mA ω ^ 2 * k330c_mB) * (ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k330c_mA, k330c_mB, Matrix.mul_apply, Fin.sum_univ_three, pow_two] <;>
    ring_nf <;>
    simp only [h2, h3, k330c_om4 h3, k330c_om5 h2 h3, k330c_om6 h3, k330c_om7 h3,
      k330c_om8 h2 h3, k330c_om9 h3, k330c_om12 h3, pow_one, pow_zero] <;>
    ring

end Matrices

section Groups

variable {K : Type} [Field K]

private noncomputable def k330c_gA (ω : K) (h3 : ω ^ 3 = 1) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (k330c_mA ω)
    (by rw [k330c_det_mA h3]; norm_num)

private noncomputable def k330c_gB (K : Type) [Field K] : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (k330c_mB (K := K))
    (by rw [k330c_det_mB (K := K)]; norm_num)

private noncomputable def k330c_gT (ω : K) (hω0 : ω ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (k330c_mT ω)
    (by rw [k330c_det_mT]; exact hω0)

private noncomputable def k330c_gU (ω : K) (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hδ : (1 : K) - ω ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((1 - ω)⁻¹ • k330c_mF ω)
    (by
      rw [Matrix.det_smul, k330c_det_mF h2 h3, Fintype.card_fin]
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hδ)]
      exact one_ne_zero)

private noncomputable def k330c_gscalar {c : K} (hc : c ≠ 0) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 c hc)

private noncomputable def k330c_gV (ω : K) (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) (hδ : (1 : K) - ω ≠ 0) : GL (Fin 3) K :=
  k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gT ω hω0)⁻¹

private lemma k330c_gA_val {ω : K} (h3 : ω ^ 3 = 1) :
    (↑(k330c_gA ω h3) : Matrix (Fin 3) (Fin 3) K) = k330c_mA ω := rfl

private lemma k330c_gB_val (K : Type) [Field K] :
    (↑(k330c_gB K) : Matrix (Fin 3) (Fin 3) K) = k330c_mB := rfl

private lemma k330c_gU_val {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hδ : (1 : K) - ω ≠ 0) :
    (↑(k330c_gU ω h2 h3 hδ) : Matrix (Fin 3) (Fin 3) K) = (1 - ω)⁻¹ • k330c_mF ω := rfl

private lemma k330c_gT_val {ω : K} (hω0 : ω ≠ 0) :
    (↑(k330c_gT ω hω0) : Matrix (Fin 3) (Fin 3) K) = k330c_mT ω := rfl

private lemma k330c_gscalar_val {c : K} (hc : c ≠ 0) :
    (↑(k330c_gscalar (K := K) (c := c) hc) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  rw [k330c_gscalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]
  simp [Units.val_mk0]

private lemma k330c_gscalar_mem {c : K} (hc : c ≠ 0) (hc3 : c ^ 3 = 1) :
    k330c_gscalar (K := K) (c := c) hc ∈ StatedSL 3 K := by
  apply StatedAPI.mem_statedSL_of_det
  rw [k330c_gscalar_val, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  exact hc3

private lemma k330c_mem_scalars_iff {x : StatedSL 3 K} :
    x ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) ↔
      ∃ c : K, ((↑x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars]
  constructor
  · rintro ⟨u, hu⟩
    have h := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hu
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h
    refine ⟨(u : K), ?_⟩
    rw [Matrix.smul_one_eq_diagonal]
    exact h.symm
  · rintro ⟨c, hc⟩
    have hdet : ((↑x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      StatedAPI.mem_statedSL_iff.mp x.2
    have hc0 : c ≠ 0 := by
      intro hc0
      have h3 : ((↑x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = c ^ 3 := by
        rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
      rw [hdet, hc0, zero_pow (by norm_num : 3 ≠ 0)] at h3
      exact one_ne_zero h3
    exact ⟨Units.mk0 c hc0, by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
        ← Matrix.smul_one_eq_diagonal]
      exact hc.symm⟩

private lemma k330c_gA_cube {ω : K} (h3 : ω ^ 3 = 1) : k330c_gA ω h3 ^ 3 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_one]
  rw [k330c_gA_val, k330c_mA_cube h3]

private lemma k330c_gB_cube (K : Type) [Field K] : k330c_gB K ^ 3 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_one]
  rw [k330c_gB_val, k330c_mB_cube]

private lemma k330c_gA_gB_scalar {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) :
    k330c_gA ω h3 * k330c_gB K =
      (k330c_gB K * k330c_gA ω h3) * k330c_gscalar (K := K) (c := ω) hω0 := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  rw [k330c_gA_val, k330c_gB_val, k330c_gscalar_val]
  rw [mul_smul_comm, Matrix.mul_one]
  exact k330c_mA_mB h2 h3

private lemma k330c_gA_gB_gA_scalar {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) :
    k330c_gA ω h3 * k330c_gB K * k330c_gA ω h3 =
      (k330c_gA ω h3 ^ 2 * k330c_gB K) *
        k330c_gscalar (K := K) (c := ω ^ 2) (pow_ne_zero 2 hω0) := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_mul]
  rw [k330c_gA_val, k330c_gB_val, k330c_gscalar_val]
  exact k330c_mA_mB_mA h2 h3

private lemma k330c_gU_gA {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hδ : (1 : K) - ω ≠ 0) :
    k330c_gU ω h2 h3 hδ * k330c_gA ω h3 * (k330c_gU ω h2 h3 hδ)⁻¹ =
      (k330c_gB K)⁻¹ := by
  have h : k330c_gU ω h2 h3 hδ * k330c_gA ω h3 =
      (k330c_gB K)⁻¹ * k330c_gU ω h2 h3 hδ := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
    rw [k330c_gA_val, k330c_gB_val, k330c_gU_val, k330c_mB_inv]
    rw [smul_mul_assoc, mul_smul_comm, k330c_mF_mA h2 h3]
  calc k330c_gU ω h2 h3 hδ * k330c_gA ω h3 * (k330c_gU ω h2 h3 hδ)⁻¹
      = ((k330c_gB K)⁻¹ * k330c_gU ω h2 h3 hδ) * (k330c_gU ω h2 h3 hδ)⁻¹ := by rw [h]
    _ = (k330c_gB K)⁻¹ := by group

private lemma k330c_gU_gB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hδ : (1 : K) - ω ≠ 0) :
    k330c_gU ω h2 h3 hδ * k330c_gB K * (k330c_gU ω h2 h3 hδ)⁻¹ = k330c_gA ω h3 := by
  have h : k330c_gU ω h2 h3 hδ * k330c_gB K = k330c_gA ω h3 * k330c_gU ω h2 h3 hδ := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [k330c_gA_val, k330c_gB_val, k330c_gU_val]
    rw [smul_mul_assoc, mul_smul_comm, k330c_mF_mB h2 h3]
  calc k330c_gU ω h2 h3 hδ * k330c_gB K * (k330c_gU ω h2 h3 hδ)⁻¹
      = (k330c_gA ω h3 * k330c_gU ω h2 h3 hδ) * (k330c_gU ω h2 h3 hδ)⁻¹ := by rw [h]
    _ = k330c_gA ω h3 := by group

private lemma k330c_gT_gB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) :
    k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹ = k330c_gB K * k330c_gA ω h3 := by
  have h : k330c_gT ω hω0 * k330c_gB K = (k330c_gB K * k330c_gA ω h3) * k330c_gT ω hω0 := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [k330c_gA_val, k330c_gB_val, k330c_gT_val, k330c_mT_mB h2 h3]
  calc k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹
      = ((k330c_gB K * k330c_gA ω h3) * k330c_gT ω hω0) * (k330c_gT ω hω0)⁻¹ := by rw [h]
    _ = k330c_gB K * k330c_gA ω h3 := by group

private lemma k330c_gV_gA {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) (hδ : (1 : K) - ω ≠ 0) :
    k330c_gV ω h2 h3 hω0 hδ * k330c_gA ω h3 * (k330c_gV ω h2 h3 hω0 hδ)⁻¹ =
      k330c_gA ω h3 ^ 2 * (k330c_gB K) ^ 2 := by
  have hcomm : k330c_gT ω hω0 * k330c_gA ω h3 = k330c_gA ω h3 * k330c_gT ω hω0 := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [k330c_gA_val, k330c_gT_val, k330c_mT_mA]
  have hTinvA : (k330c_gT ω hω0)⁻¹ * k330c_gA ω h3 * k330c_gT ω hω0 = k330c_gA ω h3 := by
    calc (k330c_gT ω hω0)⁻¹ * k330c_gA ω h3 * k330c_gT ω hω0
        = (k330c_gT ω hω0)⁻¹ * (k330c_gA ω h3 * k330c_gT ω hω0) := by group
      _ = (k330c_gT ω hω0)⁻¹ * (k330c_gT ω hω0 * k330c_gA ω h3) := by rw [hcomm]
      _ = k330c_gA ω h3 := by group
  have hTB := k330c_gT_gB (K := K) h2 h3 hω0
  have hUA := k330c_gU_gA (K := K) h2 h3 hδ
  have hAinv : (k330c_gA ω h3)⁻¹ = k330c_gA ω h3 ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ' (k330c_gA ω h3) 2]; exact k330c_gA_cube h3)
  have hBinv : (k330c_gB K)⁻¹ = (k330c_gB K) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ' (k330c_gB K) 2]; exact k330c_gB_cube K)
  rw [k330c_gV]
  calc (k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gT ω hω0)⁻¹) * k330c_gA ω h3 *
        (k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gT ω hω0)⁻¹)⁻¹
      = k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ *
          ((k330c_gT ω hω0)⁻¹ * k330c_gA ω h3 * k330c_gT ω hω0) *
          (k330c_gU ω h2 h3 hδ)⁻¹ * (k330c_gT ω hω0)⁻¹ := by group
    _ = k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * k330c_gA ω h3 *
          (k330c_gU ω h2 h3 hδ)⁻¹ * (k330c_gT ω hω0)⁻¹ := by rw [hTinvA]
    _ = k330c_gT ω hω0 * (k330c_gU ω h2 h3 hδ * k330c_gA ω h3 *
          (k330c_gU ω h2 h3 hδ)⁻¹) * (k330c_gT ω hω0)⁻¹ := by group
    _ = k330c_gT ω hω0 * (k330c_gB K)⁻¹ * (k330c_gT ω hω0)⁻¹ := by rw [hUA]
    _ = (k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹)⁻¹ := by group
    _ = (k330c_gB K * k330c_gA ω h3)⁻¹ := by rw [hTB]
    _ = (k330c_gA ω h3)⁻¹ * (k330c_gB K)⁻¹ := by group
    _ = k330c_gA ω h3 ^ 2 * (k330c_gB K) ^ 2 := by rw [hAinv, hBinv]

private lemma k330c_gV_gB {ω : K} (h2 : ω ^ 2 = -1 - ω) (h3 : ω ^ 3 = 1)
    (hω0 : ω ≠ 0) (hδ : (1 : K) - ω ≠ 0) :
    k330c_gV ω h2 h3 hω0 hδ * k330c_gB K * (k330c_gV ω h2 h3 hω0 hδ)⁻¹ =
      k330c_gA ω h3 * k330c_gB K * k330c_gA ω h3 := by
  have hcomm : k330c_gT ω hω0 * k330c_gA ω h3 = k330c_gA ω h3 * k330c_gT ω hω0 := by
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [k330c_gA_val, k330c_gT_val, k330c_mT_mA]
  have hTinvA : (k330c_gT ω hω0)⁻¹ * k330c_gA ω h3 * k330c_gT ω hω0 = k330c_gA ω h3 := by
    calc (k330c_gT ω hω0)⁻¹ * k330c_gA ω h3 * k330c_gT ω hω0
        = (k330c_gT ω hω0)⁻¹ * (k330c_gA ω h3 * k330c_gT ω hω0) := by group
      _ = (k330c_gT ω hω0)⁻¹ * (k330c_gT ω hω0 * k330c_gA ω h3) := by rw [hcomm]
      _ = k330c_gA ω h3 := by group
  have hTB := k330c_gT_gB (K := K) h2 h3 hω0
  have hTB' : k330c_gT ω hω0 * k330c_gB K =
      k330c_gB K * k330c_gA ω h3 * k330c_gT ω hω0 := by
    calc k330c_gT ω hω0 * k330c_gB K
        = (k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹) * k330c_gT ω hω0 := by group
      _ = k330c_gB K * k330c_gA ω h3 * k330c_gT ω hω0 := by rw [hTB]
  have hTinvB : (k330c_gT ω hω0)⁻¹ * k330c_gB K * k330c_gT ω hω0 =
      k330c_gB K * (k330c_gA ω h3)⁻¹ := by
    have h : k330c_gT ω hω0 *
          ((k330c_gT ω hω0)⁻¹ * k330c_gB K * k330c_gT ω hω0) * k330c_gA ω h3 =
        k330c_gT ω hω0 * (k330c_gB K * (k330c_gA ω h3)⁻¹) * k330c_gA ω h3 := by
      rw [show k330c_gT ω hω0 * ((k330c_gT ω hω0)⁻¹ * k330c_gB K * k330c_gT ω hω0) *
          k330c_gA ω h3 = k330c_gB K * (k330c_gT ω hω0 * k330c_gA ω h3) by group]
      rw [hcomm]
      rw [show k330c_gB K * (k330c_gA ω h3 * k330c_gT ω hω0) =
          k330c_gB K * k330c_gA ω h3 * k330c_gT ω hω0 by group]
      rw [show k330c_gT ω hω0 * (k330c_gB K * (k330c_gA ω h3)⁻¹) * k330c_gA ω h3 =
          k330c_gT ω hω0 * k330c_gB K by group]
      exact hTB'.symm
    exact mul_left_cancel (mul_right_cancel h)
  have hUB := k330c_gU_gB (K := K) h2 h3 hδ
  have hUinvA : k330c_gU ω h2 h3 hδ * (k330c_gA ω h3)⁻¹ * (k330c_gU ω h2 h3 hδ)⁻¹ =
      k330c_gB K := by
    calc k330c_gU ω h2 h3 hδ * (k330c_gA ω h3)⁻¹ * (k330c_gU ω h2 h3 hδ)⁻¹
        = (k330c_gU ω h2 h3 hδ * k330c_gA ω h3 * (k330c_gU ω h2 h3 hδ)⁻¹)⁻¹ := by group
      _ = ((k330c_gB K)⁻¹)⁻¹ := by rw [k330c_gU_gA h2 h3 hδ]
      _ = k330c_gB K := by group
  rw [k330c_gV]
  calc (k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gT ω hω0)⁻¹) * k330c_gB K *
        (k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gT ω hω0)⁻¹)⁻¹
      = k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ *
          ((k330c_gT ω hω0)⁻¹ * k330c_gB K * k330c_gT ω hω0) *
          (k330c_gU ω h2 h3 hδ)⁻¹ * (k330c_gT ω hω0)⁻¹ := by group
    _ = k330c_gT ω hω0 * k330c_gU ω h2 h3 hδ * (k330c_gB K * (k330c_gA ω h3)⁻¹) *
          (k330c_gU ω h2 h3 hδ)⁻¹ * (k330c_gT ω hω0)⁻¹ := by rw [hTinvB]
    _ = k330c_gT ω hω0 * (k330c_gU ω h2 h3 hδ * k330c_gB K * (k330c_gA ω h3)⁻¹ *
          (k330c_gU ω h2 h3 hδ)⁻¹) * (k330c_gT ω hω0)⁻¹ := by group
    _ = k330c_gT ω hω0 * ((k330c_gU ω h2 h3 hδ * k330c_gB K * (k330c_gU ω h2 h3 hδ)⁻¹) *
          (k330c_gU ω h2 h3 hδ * (k330c_gA ω h3)⁻¹ *
            (k330c_gU ω h2 h3 hδ)⁻¹)) * (k330c_gT ω hω0)⁻¹ := by group
    _ = k330c_gT ω hω0 * (k330c_gA ω h3 * k330c_gB K) * (k330c_gT ω hω0)⁻¹ := by
          rw [hUB, hUinvA]
    _ = k330c_gA ω h3 * (k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹) := by
          calc k330c_gT ω hω0 * (k330c_gA ω h3 * k330c_gB K) * (k330c_gT ω hω0)⁻¹
              = (k330c_gT ω hω0 * k330c_gA ω h3) * k330c_gB K * (k330c_gT ω hω0)⁻¹ := by
                group
            _ = (k330c_gA ω h3 * k330c_gT ω hω0) * k330c_gB K * (k330c_gT ω hω0)⁻¹ := by
                rw [hcomm]
            _ = k330c_gA ω h3 * (k330c_gT ω hω0 * k330c_gB K * (k330c_gT ω hω0)⁻¹) := by
                group
    _ = k330c_gA ω h3 * (k330c_gB K * k330c_gA ω h3) := by rw [hTB]
    _ = k330c_gA ω h3 * k330c_gB K * k330c_gA ω h3 := by group

end Groups

private theorem k330c_hasHeis_of_mulEquiv {J T : Type} [Group J] [Group T] (e : J ≃* T)
    (h : HasHeis T) : HasHeis J := by
  obtain ⟨a, b, u, v, hab, ha3, hb3, hcard, hua, hub, hva, hvb⟩ := h
  refine ⟨e.symm a, e.symm b, e.symm u, e.symm v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg e.symm hab
  · simpa only [map_pow, map_one] using congrArg e.symm ha3
  · simpa only [map_pow, map_one] using congrArg e.symm hb3
  · rw [show Subgroup.closure ({e.symm a, e.symm b} : Set J) =
        (Subgroup.closure ({a, b} : Set T)).map e.symm.toMonoidHom by
      rw [MonoidHom.map_closure]
      congr 1
      ext x
      simp]
    rw [Subgroup.card_map_of_injective e.symm.injective, hcard]
  · simpa only [map_mul, map_inv] using congrArg e.symm hua
  · simpa only [map_mul, map_inv] using congrArg e.symm hub
  · simpa only [map_mul, map_inv, map_pow] using congrArg e.symm hva
  · simpa only [map_mul, map_inv, map_pow] using congrArg e.symm hvb

private theorem k330c_hasHeis_statedProj (K : Type) [Field K] [Finite K]
    (h3dvd : 3 ∣ Nat.card K - 1) : HasHeis (StatedProj (StatedSL 3 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  let ω : K := ζ
  have hω3 : ω ^ 3 = 1 := by
    have h : ζ ^ 3 = 1 := by rw [← hζ, pow_orderOf_eq_one]
    simpa [ω, Units.val_pow_eq_pow_val] using congrArg (fun u : Kˣ => (u : K)) h
  have hω1 : ω ≠ 1 := by
    intro h
    have hz : ζ = 1 := Units.ext h
    rw [hz] at hζ
    simp at hζ
  have hω0 : ω ≠ 0 := by
    intro h
    have h0 : ω ^ 3 = 0 := by rw [h]; ring
    rw [hω3] at h0
    exact one_ne_zero h0
  have h2 : ω ^ 2 = -1 - ω := by
    have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      rw [show (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 by ring, hω3]; ring
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hω1
    · linear_combination h'
  have hδ : (1 : K) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have hω20 : ω ^ 2 ≠ 0 := pow_ne_zero 2 hω0
  let H := StatedSL 3 K
  let N : Subgroup H := (StatedScalars (Fin 3) K).subgroupOf H
  let Ah : H := ⟨k330c_gA ω hω3,
    StatedAPI.mem_statedSL_of_det (by rw [k330c_gA_val, k330c_det_mA hω3])⟩
  let Bh : H := ⟨k330c_gB K,
    StatedAPI.mem_statedSL_of_det (by rw [k330c_gB_val, k330c_det_mB])⟩
  let Uh : H := ⟨k330c_gU ω h2 hω3 hδ,
    StatedAPI.mem_statedSL_of_det (by
      rw [k330c_gU_val, Matrix.det_smul, k330c_det_mF h2 hω3, Fintype.card_fin, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 3 hδ)])⟩
  let gV : GL (Fin 3) K := k330c_gV ω h2 hω3 hω0 hδ
  have hgU_det : Matrix.GeneralLinearGroup.det (k330c_gU ω h2 hω3 hδ) = 1 := by
    apply Units.ext
    change (↑(k330c_gU ω h2 hω3 hδ) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [k330c_gU_val, Matrix.det_smul, k330c_det_mF h2 hω3, Fintype.card_fin, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 3 hδ)]
  have hV_det : (↑gV : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det gV = 1 := by
      rw [show gV = k330c_gT ω hω0 * k330c_gU ω h2 hω3 hδ * (k330c_gT ω hω0)⁻¹ from rfl,
        map_mul, map_mul, map_inv, hgU_det, mul_one, mul_inv_cancel]
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
      congrArg Units.val h1
  let Vh : H := ⟨gV, StatedAPI.mem_statedSL_of_det hV_det⟩
  let Sω : H := ⟨k330c_gscalar (K := K) (c := ω) hω0, k330c_gscalar_mem hω0 hω3⟩
  let Sω2 : H := ⟨k330c_gscalar (K := K) (c := ω ^ 2) hω20,
    k330c_gscalar_mem hω20 (by rw [← pow_mul, show (2 * 3 : ℕ) = 6 by norm_num,
      k330c_om6 hω3])⟩
  have hSω_mem : Sω ∈ N := by
    rw [Subgroup.mem_subgroupOf, StatedScalars]
    exact ⟨Units.mk0 ω hω0, rfl⟩
  have hSω2_mem : Sω2 ∈ N := by
    rw [Subgroup.mem_subgroupOf, StatedScalars]
    exact ⟨Units.mk0 (ω ^ 2) hω20, rfl⟩
  let π : H →* StatedProj (StatedSL 3 K) := QuotientGroup.mk' N
  have hUA_H : Uh * Ah * Uh⁻¹ = Bh⁻¹ := by
    apply Subtype.ext
    exact k330c_gU_gA (K := K) h2 hω3 hδ
  have hUB_H : Uh * Bh * Uh⁻¹ = Ah := by
    apply Subtype.ext
    exact k330c_gU_gB (K := K) h2 hω3 hδ
  have hVA_H : Vh * Ah * Vh⁻¹ = Ah ^ 2 * Bh ^ 2 := by
    apply Subtype.ext
    exact k330c_gV_gA (K := K) h2 hω3 hω0 hδ
  have hVB_H : Vh * Bh * Vh⁻¹ = Ah * Bh * Ah := by
    apply Subtype.ext
    exact k330c_gV_gB (K := K) h2 hω3 hω0 hδ
  have hAB_H : Ah * Bh = (Bh * Ah) * Sω := by
    apply Subtype.ext
    exact k330c_gA_gB_scalar (K := K) h2 hω3 hω0
  have hABA_H : Ah * Bh * Ah = (Ah ^ 2 * Bh) * Sω2 := by
    apply Subtype.ext
    exact k330c_gA_gB_gA_scalar (K := K) h2 hω3 hω0
  let a : StatedProj (StatedSL 3 K) := π Ah
  let b : StatedProj (StatedSL 3 K) := π Bh
  let u : StatedProj (StatedSL 3 K) := π Uh
  let v : StatedProj (StatedSL 3 K) := π Vh
  have ha3 : a ^ 3 = 1 := by
    have hA3_H : Ah ^ 3 = 1 := by
      apply Subtype.ext
      exact k330c_gA_cube hω3
    rw [show a = π Ah from rfl, ← map_pow, hA3_H, map_one]
  have hb3 : b ^ 3 = 1 := by
    have hB3_H : Bh ^ 3 = 1 := by
      apply Subtype.ext
      exact k330c_gB_cube K
    rw [show b = π Bh from rfl, ← map_pow, hB3_H, map_one]
  have ha_ne_one : a ≠ 1 := by
    intro ha
    have hmem : Ah ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact ha
    obtain ⟨c, hc⟩ := k330c_mem_scalars_iff.mp hmem
    exact k330c_mA_not_scalar hω1 (by simpa [Ah, k330c_gA_val] using hc)
  have hb_ne_one : b ≠ 1 := by
    intro hb
    have hmem : Bh ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact hb
    obtain ⟨c, hc⟩ := k330c_mem_scalars_iff.mp hmem
    exact k330c_mB_not_scalar (by simpa [Bh, k330c_gB_val] using hc)
  have ha_ne_b : a ≠ b := by
    intro hab_eq
    have h1 : π (Ah * Bh⁻¹) = 1 := by
      rw [map_mul, map_inv, show π Ah = a from rfl, show π Bh = b from rfl, hab_eq,
        mul_inv_cancel]
    have hmem : Ah * Bh⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (Ah * Bh⁻¹), ← QuotientGroup.mk'_apply]
      exact h1
    obtain ⟨c, hc⟩ := k330c_mem_scalars_iff.mp hmem
    exact k330c_mA_mBtranspose_not_scalar (by
      simpa [Ah, Bh, Subgroup.coe_mul, Subgroup.coe_inv, k330c_gA_val, k330c_gB_val,
        Matrix.GeneralLinearGroup.coe_inv, k330c_mB_inv] using hc)
  have ha_ne_b2 : a ≠ b ^ 2 := by
    intro hab_eq
    have h1 : π (Ah * Bh) = 1 := by
      rw [map_mul, show π Ah = a from rfl, show π Bh = b from rfl, hab_eq, ← pow_succ, hb3]
    have hmem : Ah * Bh ∈ N := by
      rw [← QuotientGroup.eq_one_iff (Ah * Bh), ← QuotientGroup.mk'_apply]
      exact h1
    obtain ⟨c, hc⟩ := k330c_mem_scalars_iff.mp hmem
    exact k330c_mA_mB_not_scalar hω0 (by
      simpa [Ah, Bh, Subgroup.coe_mul, k330c_gA_val, k330c_gB_val] using hc)
  have ha_order : orderOf a = 3 := orderOf_eq_prime ha3 ha_ne_one
  have hb_order : orderOf b = 3 := orderOf_eq_prime hb3 hb_ne_one
  have ha_not_zpow : a ∉ Subgroup.zpowers b := by
    intro ha_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha_mem
    have hk' : b ^ (k % (3 : ℤ)) = a := by
      rw [← zpow_mod_orderOf b k, hb_order] at hk
      exact hk
    have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    have hge : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hb3' : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
    rcases hb3' with h0 | h1 | h2'
    · rw [h0, zpow_zero] at hk'
      exact ha_ne_one hk'.symm
    · rw [h1, zpow_one] at hk'
      exact ha_ne_b hk'.symm
    · rw [h2', zpow_ofNat] at hk'
      exact ha_ne_b2 hk'.symm
  have hab : a * b = b * a := by
    have hz : (Ah * Bh) * Sω⁻¹ = Bh * Ah := by rw [hAB_H]; group
    have h := (QuotientGroup.mk'_eq_mk' (N := N)).mpr ⟨Sω⁻¹, N.inv_mem hSω_mem, hz⟩
    simpa only [a, b, map_mul] using h
  refine ⟨a, b, u, v, hab, ha3, hb3, ?_, ?_, ?_, ?_, ?_⟩
  · have hclosure : Subgroup.closure ({a, b} : Set (StatedProj (StatedSL 3 K))) =
        Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
      rw [show ({a, b} : Set (StatedProj (StatedSL 3 K))) = {a} ∪ {b} from
        (Set.singleton_union (a := a) (s := ({b} : Set (StatedProj (StatedSL 3 K))))).symm]
      rw [Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
    rw [hclosure]
    have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (show Commute a b from hab).zpow_zpow m n
    have hzpow_a : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, ha_order]
    have hzpow_b : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, hb_order]
    have hinf : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) = 1 := by
      by_contra hne
      have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) ∣ 3 := by
        have h := Subgroup.card_dvd_of_le (H := Subgroup.zpowers a ⊓ Subgroup.zpowers b)
          (K := Subgroup.zpowers a) inf_le_left
        rwa [hzpow_a] at h
      have h3 : Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) = 3 := by
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h1 | h3
        · exact absurd h1 hne
        · exact h3
      have heq : Subgroup.zpowers a ⊓ Subgroup.zpowers b = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hzpow_a])
      exact ha_not_zpow (Subgroup.mem_inf.mp (by rw [heq]; exact Subgroup.mem_zpowers a)).2
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers a) (Subgroup.zpowers b) hcomm).1
    rw [hinf, hzpow_a, hzpow_b] at h
    simpa using h
  · have h := congrArg π hUA_H
    simpa only [u, a, b, map_mul, map_inv] using h
  · have h := congrArg π hUB_H
    simpa only [u, a, b, map_mul, map_inv] using h
  · have h := congrArg π hVA_H
    simpa only [v, a, b, map_mul, map_inv, map_pow] using h
  · have hABA : π (Ah * Bh * Ah) = π (Ah ^ 2 * Bh) := by
      have hz : (Ah * Bh * Ah) * Sω2⁻¹ = Ah ^ 2 * Bh := by rw [hABA_H]; group
      exact (QuotientGroup.mk'_eq_mk' (N := N)).mpr ⟨Sω2⁻¹, N.inv_mem hSω2_mem, hz⟩
    calc v * b * v⁻¹ = π Vh * π Bh * (π Vh)⁻¹ := rfl
      _ = π (Vh * Bh * Vh⁻¹) := by simp only [map_mul, map_inv]
      _ = π (Ah * Bh * Ah) := by rw [hVB_H]
      _ = π (Ah ^ 2 * Bh) := hABA
      _ = a ^ 2 * b := by simp only [a, b, map_mul, map_pow]

theorem hasHeis_PSL3 {J : Type} [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSL 3 p f)
    (hq : p ^ f % 3 = 1) : HasHeis J := by
  have hclass := LieModel.statedClassicalModel e (by decide)
  rw [StatedClassicalModel] at hclass
  obtain ⟨-, K, hKfield, hKfin, hKcard, ⟨eJ⟩⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have h3dvd : 3 ∣ Nat.card K - 1 := by rw [hKcard]; omega
  exact k330c_hasHeis_of_mulEquiv eJ (k330c_hasHeis_statedProj K h3dvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
