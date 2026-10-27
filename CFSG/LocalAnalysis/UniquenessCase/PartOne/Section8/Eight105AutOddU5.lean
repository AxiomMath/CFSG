module

public import CFSG.RankThree.PartOne.KF.R56Final
public import CFSG.RankThree.PartOne.KF.R6Levi
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUAut
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

open Matrix Subgroup
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.Open (StatedScalars)
open CFSG.LieType.Universal.Unitary (SU mem_SU isQuasisimple_statedSU_of_card equivStatedSU
  map_center_mulEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (b6 suBlock6 dvec5 diagU coe_b6 coe_suBlock6 blk6 diagU_val
  diagU_inv)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar (suToStated wittMat wittMat_spec
  coe_suToStated)
open CFSG.ComponentClassification.RankTwoClassical (exists_unitary_semilinear_statedProj)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem eq_of_mul_shift_fin_two (τ τ' : K) {Y : Matrix (Fin 2) (Fin 2) K} (hY : Y ≠ 0)
    (h : Y * !![τ', 1; 1, 0] = !![τ, 1; 1, 0] * Y) : τ' = τ := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  by_contra hne
  have hne' : τ' - τ ≠ 0 := sub_ne_zero.mpr hne
  have hkey : Y 0 1 * (τ' - τ) = 0 := by
    rw [mul_sub, sub_eq_zero]
    rw [h11] at h10
    calc Y 0 1 * τ' = Y 0 1 * τ' + Y 1 1 - Y 1 1 := by ring
      _ = Y 0 0 - Y 1 1 := by rw [h10]
      _ = (τ * Y 0 1 + Y 1 1) - Y 1 1 := by rw [h01]
      _ = Y 0 1 * τ := by ring
  have hy01 : Y 0 1 = 0 := by
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd h hne'
  have hy10 : Y 1 0 = 0 := by rw [h11, hy01]
  have hy00 : Y 0 0 = 0 := by
    by_contra hy0
    have hkey2 : Y 0 0 * (τ' - τ) = 0 := by
      rw [mul_sub, sub_eq_zero]
      calc Y 0 0 * τ' = Y 0 0 * τ' + Y 0 1 - Y 0 1 := by ring
        _ = (τ * Y 0 0 + Y 1 0) - Y 0 1 := by rw [h00]
        _ = Y 0 0 * τ := by rw [hy01, hy10]; ring
    rcases mul_eq_zero.1 hkey2 with h | h
    · exact hy0 h
    · exact hne' h
  have hy11 : Y 1 1 = 0 := by
    have := h01
    rw [hy00, hy01, mul_zero, zero_add] at this
    exact this.symm
  apply hY
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hy00, hy01, hy10, hy11]

omit [Finite K] [CharP K 2] in
theorem eq_zero_of_mul_diagonal_eq_diagonal_mul {d d' : Fin 5 → K}
    {Bm : Matrix (Fin 5) (Fin 5) K} (h : Bm * diagonal d' = diagonal d * Bm)
    {i j : Fin 5} (hij : d i ≠ d' j) : Bm i j = 0 := by
  have hentry := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hkey : Bm i j * (d' j - d i) = 0 := by
    linear_combination hentry
  rcases mul_eq_zero.1 hkey with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.1 h0).symm hij

omit [Finite K] [CharP K 2] in
theorem mul_eq_of_conj_eq {B M : GL (Fin 5) K} (h : B * M * B⁻¹ = M) : B * M = M * B := by
  calc B * M = (B * M * B⁻¹) * B := by group
    _ = M * B := by rw [h]

omit [Finite K] [CharP K 2] in
theorem commute_upper_unitriangular_fin_two {X : Matrix (Fin 2) (Fin 2) K}
    (h : X * !![1, 1; 0, 1] = !![1, 1; 0, 1] * X) :
    X 1 0 = 0 ∧ X 0 0 = X 1 1 := by
  constructor
  · have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact h00
  · have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    rw [add_comm (X 0 1) (X 1 1)] at h01
    exact add_right_cancel h01

omit [Finite K] [CharP K 2] in
theorem commute_lower_unitriangular_fin_two {X : Matrix (Fin 2) (Fin 2) K}
    (h : X * !![1, 0; 1, 1] = !![1, 0; 1, 1] * X) :
    X 0 1 = 0 ∧ X 0 0 = X 1 1 := by
  constructor
  · have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
    exact h00
  · have h10 := congrFun (congrFun h 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h10
    rw [add_comm (X 0 0) (X 1 0)] at h10
    exact (add_left_cancel h10).symm

theorem pow_five_of_conj_smul_b6 {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {φ : K ≃+* K} {B : GL (Fin 5) K} {u : Kˣ}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
    (u : K) ^ 5 = 1 := by
  classical
  let N : ↥(SU (unitaryInvolution K 2 2) 5) := b6 (unitaryInvolution K 2 2) ζ hζ
  have hN : N = b6 (unitaryInvolution K 2 2) ζ hζ := rfl
  have hNdet : ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
    have := (mem_SU.1 N.2).1
    simpa [N] using this
  have hMdet : (((glAut φ (N : GL (Fin 5) K) : GL (Fin 5) K)) :
      Matrix (Fin 5) (Fin 5) K).det = 1 := by
    rw [coe_glAut]
    change ((φ : K →+* K).mapMatrix ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).det = 1
    rw [← RingHom.map_det, hNdet, map_one]
  have hscalar_det : (((GeneralLinearGroup.scalar (Fin 5) u : GL (Fin 5) K)) :
      Matrix (Fin 5) (Fin 5) K).det = (u : K) ^ 5 := by
    rw [GeneralLinearGroup.coe_scalar]
    change (diagonal (fun _ : Fin 5 => (u : K))).det = (u : K) ^ 5
    rw [det_diagonal]
    simp
  have hdet := congrArg (fun x : GL (Fin 5) K =>
    ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det) h
  rw [Units.val_mul, Units.val_mul,
    Matrix.det_units_conj B (((glAut φ (N : GL (Fin 5) K) : GL (Fin 5) K)) :
      Matrix (Fin 5) (Fin 5) K),
    hMdet, Units.val_mul, Matrix.det_mul, hscalar_det, hNdet, mul_one] at hdet
  exact hdet.symm

omit [Finite K] [CharP K 2] in
theorem mem_one_or_zeta_of_dvec5_inv {ζ u : Kˣ} {i : Fin 5}
    (h : u = (dvec5 ζ ζ i)⁻¹) : u = 1 ∨ u = ζ ∨ u = ζ⁻¹ := by
  fin_cases i <;> simp [dvec5] at h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inl h)

theorem matrix_relation_of_conj_smul_b6 {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {φ : K ≃+* K} {B : GL (Fin 5) K} {u : Kˣ}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
    (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *
        ((((glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) : GL (Fin 5) K)) :
          Matrix (Fin 5) (Fin 5) K)) =
      (diagonal (fun _ : Fin 5 => (u : K)) *
        (((b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
          Matrix (Fin 5) (Fin 5) K)) *
        (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) := by
  have hD : ((GeneralLinearGroup.scalar (Fin 5) u : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = diagonal (fun _ : Fin 5 => (u : K)) := by
    rw [GeneralLinearGroup.coe_scalar]
    rfl
  have hBmatGL : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) =
      (GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) * B := by
    calc B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) =
        (B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹) * B := by
          group
      _ = (GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) * B := by rw [h]
  have hh := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
    Matrix (Fin 5) (Fin 5) K)) hBmatGL
  simpa only [Units.val_mul, hD] using hh

theorem exists_eigenvector_of_conj_smul_b6 {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {φ : K ≃+* K} {B : GL (Fin 5) K} {u : Kˣ}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
    ∃ i : Fin 5, (u : K) * (dvec5 ζ ζ i : K) = 1 := by
  classical
  let v : Fin 5 → K := fun i => (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) i 2
  have hBmat := matrix_relation_of_conj_smul_b6 hζ h
  have hvne : v ≠ 0 := by
    intro hv0
    have hdet0 : (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero 2 (fun i => congrFun hv0 i)
    exact B.det_ne_zero hdet0
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hvne (funext fun i => hcon i)
  have hleft : ((((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *
      ((((glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) : GL (Fin 5) K)) :
        Matrix (Fin 5) (Fin 5) K))) i 2 = v i := by
    rw [Matrix.mul_apply, coe_glAut, coe_b6, diagU_val]
    simp [v, dvec5, Matrix.diagonal_apply, Fin.sum_univ_five]
  have hright : ((diagonal (fun _ : Fin 5 => (u : K)) *
      (((b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
        Matrix (Fin 5) (Fin 5) K)) *
        (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) i 2 =
          ((u : K) * (dvec5 ζ ζ i : K)) * v i := by
    rw [coe_b6, diagU_val, Matrix.diagonal_mul_diagonal, Matrix.mul_apply]
    simp [v, dvec5, Matrix.diagonal_apply]
  have hvi : v i = ((u : K) * (dvec5 ζ ζ i : K)) * v i := by
    calc v i = ((((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *
        ((((glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) : GL (Fin 5) K)) :
          Matrix (Fin 5) (Fin 5) K))) i 2 := hleft.symm
      _ = ((diagonal (fun _ : Fin 5 => (u : K)) *
        (((b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
          Matrix (Fin 5) (Fin 5) K)) *
          (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) i 2 :=
            congrFun (congrFun hBmat i) 2
      _ = ((u : K) * (dvec5 ζ ζ i : K)) * v i := hright
  have hudi : (u : K) * (dvec5 ζ ζ i : K) = 1 := by
    have h1i : ((u : K) * (dvec5 ζ ζ i : K)) * v i = 1 * v i := by
      rw [one_mul, ← hvi]
    exact mul_right_cancel₀ hi h1i
  exact ⟨i, hudi⟩

theorem eigenvalue_eq_inv_dvec5_of_conj_smul_b6 {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    {φ : K ≃+* K} {B : GL (Fin 5) K} {u : Kˣ}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
    ∃ i : Fin 5, u = (dvec5 ζ ζ i)⁻¹ := by
  obtain ⟨i, hi⟩ := exists_eigenvector_of_conj_smul_b6 hζ h
  refine ⟨i, ?_⟩
  apply Units.ext
  rw [Units.val_inv_eq_inv_val]
  exact (inv_eq_of_mul_eq_one_right (by rwa [mul_comm] at hi)).symm

theorem eq_one_of_conj_smul_b6 {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ)
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {φ : K ≃+* K} {B : GL (Fin 5) K} {u : Kˣ}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      GeneralLinearGroup.scalar (Fin 5) u *
        (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K)) :
    u = 1 := by
  classical
  have h5 : (u : K) ^ 5 = 1 := pow_five_of_conj_smul_b6 hζ h
  obtain ⟨i, hu_inv⟩ := eigenvalue_eq_inv_dvec5_of_conj_smul_b6 hζ h
  have hu_mem : u = 1 ∨ u = ζ ∨ u = ζ⁻¹ := mem_one_or_zeta_of_dvec5_inv hu_inv
  have hu3 : u ^ 3 = 1 := by
    rcases hu_mem with rfl | rfl | rfl
    · simp
    · exact h3
    · rw [inv_pow, h3, inv_one]
  have h5u : u ^ 5 = 1 := by
    apply Units.ext
    simpa using h5
  exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 3 5)).mp ⟨hu3, h5u⟩

omit [Finite K] [CharP K 2] in
theorem mulVec_scalar_mul_of_fix {B N : GL (Fin 5) K} {u : Kˣ} {a : K} {e : Fin 5 → K}
    (hB : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e = a • e)
    (hN : ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e = e) :
    (((GeneralLinearGroup.scalar (Fin 5) u * N : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) *ᵥ (((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e)) =
        ((u : K) * a) • e := by
  have hassoc : ∀ (M N : Matrix (Fin 5) (Fin 5) K) (v : Fin 5 → K),
      (M * N) *ᵥ v = M *ᵥ (N *ᵥ v) := by
    intro M N v
    rw [← Matrix.mulVec_mulVec]
  have hD : ((GeneralLinearGroup.scalar (Fin 5) u : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = diagonal (fun _ : Fin 5 => (u : K)) := by
    rw [GeneralLinearGroup.coe_scalar]
    rfl
  have hdiag_smul : ∀ w : Fin 5 → K,
      diagonal (fun _ : Fin 5 => (u : K)) *ᵥ w = (u : K) • w := by
    intro w
    ext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [Units.val_mul, hD]
  calc ((diagonal (fun _ : Fin 5 => (u : K)) *
      (((N : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) *ᵥ
        ((((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ e))
      = diagonal (fun _ : Fin 5 => (u : K)) *ᵥ
          ((((N : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ
            ((((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ e)) :=
        hassoc _ _ _
    _ = (u : K) • ((((N : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ
          ((((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ e)) :=
        hdiag_smul _
    _ = (u : K) • ((((N : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ (a • e)) := by
        rw [hB]
    _ = (u : K) • (a • ((((N : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) *ᵥ e)) := by
        rw [Matrix.mulVec_smul]
    _ = (u : K) • (a • e) := by rw [hN]
    _ = ((u : K) * a) • e := by rw [smul_smul]

omit [Finite K] [CharP K 2] in
theorem eq_one_of_conj_smul_of_fix {B M N : GL (Fin 5) K} {u : Kˣ} {a : K}
    {e : Fin 5 → K} (he : e 2 = 1) (ha : a ≠ 0)
    (hB : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e = a • e)
    (hM : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e = e)
    (hN : ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e = e)
    (h : B * M * B⁻¹ = GeneralLinearGroup.scalar (Fin 5) u * N) : u = 1 := by
  have hassoc : ∀ (M N : Matrix (Fin 5) (Fin 5) K) (v : Fin 5 → K),
      (M * N) *ᵥ v = M *ᵥ (N *ᵥ v) := by
    intro M N v
    rw [← Matrix.mulVec_mulVec]
  have hL : (((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        (((B⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) *ᵥ
          (((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ e) = a • e := by
    rw [hassoc, ← hassoc (((B⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
      (((B : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) e]
    rw [show (((B⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hM, hB]
  have hmat : (((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        (((B⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) =
          ((GeneralLinearGroup.scalar (Fin 5) u * N : GL (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K) := by
    change (((B * M * B⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) = _
    rw [h]
  have hR := mulVec_scalar_mul_of_fix (B := B) (N := N) (u := u) (a := a) (e := e) hB hN
  have hsum : a • e = ((u : K) * a) • e := by
    rw [← hL, hmat, hR]
  have h1 : a = (u : K) * a := by
    have := congrFun hsum 2
    simpa [he] using this
  have h1' : a * (1 : K) = a * (u : K) := by
    rw [mul_one]
    calc a = (u : K) * a := h1
      _ = a * (u : K) := mul_comm _ _
  exact (Units.ext (mul_left_cancel₀ ha h1')).symm

omit [Finite K] [CharP K 2] in
theorem dvec5_ne_one_of_ne_two {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {i : Fin 5} (hi : i ≠ 2) : (dvec5 ζ ζ i : K) ≠ 1 := by
  fin_cases i
  · simpa [dvec5] using h1
  · simpa [dvec5] using h1
  · exact absurd rfl hi
  · intro hh
    apply h2
    have hζ1 : ζ = 1 := by simpa [dvec5] using hh
    rw [hζ1]; simp
  · intro hh
    apply h2
    have hζ1 : ζ = 1 := by simpa [dvec5] using hh
    rw [hζ1]; simp

theorem exists_smul_single_of_conj_b6
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    {φ : K ≃+* K} {B : GL (Fin 5) K}
    (h : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B) :
    ∃ a : K, a ≠ 0 ∧ ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
      (Pi.single 2 (1 : K)) = a • (Pi.single 2 (1 : K)) := by
  classical
  let N : ↥(SU (unitaryInvolution K 2 2) 5) := b6 (unitaryInvolution K 2 2) ζ hζ
  have hN : N = b6 (unitaryInvolution K 2 2) ζ hζ := rfl
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  let e : Fin 5 → K := Pi.single 2 1
  let v : Fin 5 → K := fun i => Bm i 2
  have hmat' : Bm * diagonal (fun j => φ (dvec5 ζ ζ j : K)) =
      diagonal (fun j => (dvec5 ζ ζ j : K)) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) h
    simpa [Bm, hN, coe_glAut, coe_b6, diagU_val, Units.val_mul] using this
  have hζne : ∀ i : Fin 5, i ≠ 2 → (dvec5 ζ ζ i : K) ≠ 1 :=
    fun i hi => dvec5_ne_one_of_ne_two h1 h2 hi
  have hzero : ∀ i : Fin 5, i ≠ 2 → v i = 0 := by
    intro i hi
    apply eq_zero_of_mul_diagonal_eq_diagonal_mul hmat'
    rw [show (dvec5 ζ ζ 2 : K) = 1 by simp [dvec5], map_one]
    exact hζne i hi
  have hvne : v ≠ 0 := by
    intro hv0
    have hdet0 : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero 2 (fun i => congrFun hv0 i)
    exact B.det_ne_zero hdet0
  have hv2 : v 2 ≠ 0 := by
    intro hv2
    apply hvne
    funext i
    by_cases hi : i = 2
    · rw [hi]; exact hv2
    · exact hzero i hi
  refine ⟨v 2, hv2, ?_⟩
  funext i
  by_cases hi : i = 2
  · subst hi
    simp [v, Bm, Matrix.mulVec]
  · have hleft : (Bm *ᵥ Pi.single 2 1) i = v i := by
      simp [v, Bm, Matrix.mulVec]
    rw [hleft, hzero i hi]
    simp [Pi.single_eq_of_ne hi]

theorem mulVec_single_two_suBlock6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    (A : SpecialLinearGroup (Fin 2) K) :
    (((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
      ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
        Pi.single 2 (1 : K) = Pi.single 2 (1 : K) := by
  ext i
  rw [Matrix.mulVec, coe_suBlock6]
  fin_cases i <;> simp [blk6]

theorem mulVec_single_two_glAut_suBlock6 (hK : Nat.card K = (2 ^ 2) ^ 2) (φ : K ≃+* K)
    (A : SpecialLinearGroup (Fin 2) K) :
    (((glAut φ ((suBlock6 (unitaryInvolution K 2 2)
      (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
        GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)) *ᵥ
        Pi.single 2 (1 : K) = Pi.single 2 (1 : K) := by
  ext i
  rw [Matrix.mulVec, coe_glAut, coe_suBlock6]
  fin_cases i <;> simp [blk6]

theorem rel_block_top_fin_five (C : Matrix (Fin 2) (Fin 2) K) {Bm M : Matrix (Fin 5) (Fin 5) K}
    (hM : M = blk6 (unitaryInvolution K 2 2) C) (h : Bm * M = M * Bm) :
    (!![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] : Matrix (Fin 2) (Fin 2) K) * C =
      C * !![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    (have h' := congrFun (congrFun h 0) 0
     have h'' := congrFun (congrFun h 0) 1
     have h3 := congrFun (congrFun h 1) 0
     have h4 := congrFun (congrFun h 1) 1
     simp_all [blk6, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_five])

theorem rel_block_bot_fin_five (C : Matrix (Fin 2) (Fin 2) K)
    {Bm M : Matrix (Fin 5) (Fin 5) K}
    (hC : ∀ i j, unitaryInvolution K 2 2 (C i j) = C i j)
    (hM : M = blk6 (unitaryInvolution K 2 2) C) (h : Bm * M = M * Bm) :
    (!![Bm 3 3, Bm 3 4; Bm 4 3, Bm 4 4] : Matrix (Fin 2) (Fin 2) K) * C =
      C * !![Bm 3 3, Bm 3 4; Bm 4 3, Bm 4 4] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    (have h' := congrFun (congrFun h 3) 3
     have h'' := congrFun (congrFun h 3) 4
     have h3 := congrFun (congrFun h 4) 3
     have h4 := congrFun (congrFun h 4) 4
     simp_all [blk6, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_five])



theorem rel_shift_fin_two (φ : K ≃+* K) (τ : K) {Bm : Matrix (Fin 5) (Fin 5) K} {M : GL (Fin 5) K}
    (hM : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 (unitaryInvolution K 2 2) (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K))
    (h : Bm * (((glAut φ M : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm) :
    (!![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] : Matrix (Fin 2) (Fin 2) K) *
        !![φ τ, 1; 1, 0] = !![τ, 1; 1, 0] * !![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    (have h' := congrFun (congrFun h 0) 0
     have h'' := congrFun (congrFun h 0) 1
     have h3 := congrFun (congrFun h 1) 0
     have h4 := congrFun (congrFun h 1) 1
     simp_all [coe_glAut, blk6, Matrix.mul_apply, Fin.sum_univ_two,
       Fin.sum_univ_five])


omit [Finite K] [CharP K 2] in
theorem pow_fifteen_of_diagonal (hK : Nat.card K = (2 ^ 2) ^ 2)
    {B : GL (Fin 5) K} {c : Fin 5 → K} (hc0 : ∀ i, c i ≠ 0)
    (hB : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal c) :
    B ^ 15 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hB, Units.val_one]
  rw [Matrix.diagonal_pow]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Pi.pow_apply]
    have hcard : Nat.card Kˣ = 15 := by
      rw [Nat.card_units, hK]
      norm_num
    have := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 (c i) (hc0 i))
    rw [hcard] at this
    simpa using congrArg (fun x : Kˣ => (x : K)) this
  · simp [hij]


omit [Finite K] [CharP K 2] in
theorem rel_block_topright (φ σ : K ≃+* K) (τ : K) {Bm : Matrix (Fin 5) (Fin 5) K}
    {M : GL (Fin 5) K}
    (hM : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 σ (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K))
    (h : Bm * (((glAut φ M : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm) :
    (!![Bm 0 3, Bm 0 4; Bm 1 3, Bm 1 4] : Matrix (Fin 2) (Fin 2) K) *
        !![φ (σ τ), 1; 1, 0] =
      !![τ, 1; 1, 0] * !![Bm 0 3, Bm 0 4; Bm 1 3, Bm 1 4] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    (have h' := congrFun (congrFun h 0) 3
     have h'' := congrFun (congrFun h 0) 4
     have h3 := congrFun (congrFun h 1) 3
     have h4 := congrFun (congrFun h 1) 4
     simp_all [coe_glAut, blk6, Matrix.mul_apply, Fin.sum_univ_two,
       Fin.sum_univ_five])


omit [Finite K] [CharP K 2] in
theorem topLeftBlock_ne_zero_of_commute_b6 {ζ : Kˣ} (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {Bm : Matrix (Fin 5) (Fin 5) K}
    (hzero : ∀ i j : Fin 5, (dvec5 ζ ζ i : K) ≠ (dvec5 ζ ζ j : K) → Bm i j = 0)
    (hdet : Bm.det ≠ 0) :
    (!![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro hX
  have hrow0 : ∀ j, Bm 0 j = 0 := by
    intro j
    fin_cases j
    · have := congrFun (congrFun hX 0) 0
      simpa using this
    · have := congrFun (congrFun hX 0) 1
      simpa using this
    · apply hzero 0 2
      simp [dvec5, h1]
    · apply hzero 0 3
      change (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K)
      intro hh
      apply hζne
      apply Units.ext
      simpa [Units.val_inv_eq_inv_val] using hh
    · apply hzero 0 4
      change (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K)
      intro hh
      apply hζne
      apply Units.ext
      simpa [Units.val_inv_eq_inv_val] using hh
  have hdet0 : Bm.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 0 hrow0
  exact hdet hdet0

theorem fieldAut_eq_of_shift_block (hK : Nat.card K = (2 ^ 2) ^ 2)
    {φ : K ≃+* K} {B : GL (Fin 5) K}
    {Bm : Matrix (Fin 5) (Fin 5) K} (hBm : Bm = ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (hXne : (!![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] : Matrix (Fin 2) (Fin 2) K) ≠ 0)
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    ∀ τ : K, φ τ = τ := by
  intro τ
  let Aτ : SpecialLinearGroup (Fin 2) K := ⟨!![τ, 1; 1, 0], by simp [CharTwo.neg_eq]⟩
  have hAτ : ((Aτ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![τ, 1; 1, 0] := rfl
  let M : GL (Fin 5) K := ((suBlock6 (unitaryInvolution K 2 2)
    (unitaryInvolution_involutive hK) Aτ : ↥(SU (unitaryInvolution K 2 2) 5)) :
      GL (Fin 5) K)
  have hM : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 (unitaryInvolution K 2 2) (!![τ, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    have := coe_suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) Aτ
    rw [hAτ] at this
    exact this
  have hτcomm : B * glAut φ M * B⁻¹ = M := hblk Aτ
  have hτBN : B * glAut φ M = M * B := by
    calc B * glAut φ M = (B * glAut φ M * B⁻¹) * B := by group
      _ = M * B := by rw [hτcomm]
  have hτmat : Bm * (((glAut φ M : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hτBN
    simpa [hBm, Units.val_mul] using this
  have hrel := rel_shift_fin_two φ τ hM hτmat
  exact eq_of_mul_shift_fin_two τ (φ τ) hXne hrel

theorem fieldAut_eq_one_of_commute_b6_blk6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1)
    (hζne : ζ ≠ ζ⁻¹) {φ : K ≃+* K} {B : GL (Fin 5) K} (hφζ : φ ζ = ζ)
    (hcomm : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K))
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    φ = 1 := by
  classical
  let N : ↥(SU (unitaryInvolution K 2 2) 5) := b6 (unitaryInvolution K 2 2) ζ hζ
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  have hNgl : (N : GL (Fin 5) K) = diagU (dvec5 ζ ζ) := by
    simpa [N] using coe_b6 (unitaryInvolution K 2 2) ζ hζ
  have hφN : glAut φ (N : GL (Fin 5) K) = (N : GL (Fin 5) K) := by
    apply Units.ext
    ext i j
    rw [coe_glAut, hNgl, diagU_val]
    fin_cases i <;> fin_cases j <;>
      simp [dvec5, hφζ]
  have hcomm' : B * glAut φ (N : GL (Fin 5) K) * B⁻¹ = (N : GL (Fin 5) K) := hcomm
  have hBcomm : B * (N : GL (Fin 5) K) * B⁻¹ = (N : GL (Fin 5) K) := by
    rwa [hφN] at hcomm'
  have hBN : B * (N : GL (Fin 5) K) = (N : GL (Fin 5) K) * B := by
    calc B * (N : GL (Fin 5) K) = (B * (N : GL (Fin 5) K) * B⁻¹) * B := by group
      _ = (N : GL (Fin 5) K) * B := by rw [hBcomm]
  have hBmat : Bm * ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hBN
    simpa [Bm, Units.val_mul] using this
  have hzero : ∀ i j : Fin 5, (dvec5 ζ ζ i : K) ≠ (dvec5 ζ ζ j : K) → Bm i j = 0 := by
    intro i j hij
    have hentry := congrFun (congrFun hBmat i) j
    rw [Matrix.mul_apply, Matrix.mul_apply, hNgl, diagU_val] at hentry
    simp [Matrix.diagonal_apply] at hentry
    have hkey : Bm i j * ((dvec5 ζ ζ j : K) - (dvec5 ζ ζ i : K)) = 0 := by
      linear_combination hentry
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hij
  have hXne : (!![Bm 0 0, Bm 0 1; Bm 1 0, Bm 1 1] : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    topLeftBlock_ne_zero_of_commute_b6 h1 hζne hzero B.det_ne_zero
  exact RingEquiv.ext (fieldAut_eq_of_shift_block hK rfl hXne hblk)


theorem block_matrices_of_commute_b6_blk6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {B : GL (Fin 5) K}
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut (1 : K ≃+* K) (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    ∃ ME MF : GL (Fin 5) K,
      ((ME : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        blk6 (unitaryInvolution K 2 2) (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) ∧
      ((MF : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        blk6 (unitaryInvolution K 2 2) (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) ∧
      B * ME = ME * B ∧ B * MF = MF * B := by
  classical
  let CE : Matrix (Fin 2) (Fin 2) K := !![1, 1; 0, 1]
  let CF : Matrix (Fin 2) (Fin 2) K := !![1, 0; 1, 1]
  have hCEdet : CE.det = 1 := by rw [Matrix.det_fin_two_of]; simp
  have hCFdet : CF.det = 1 := by rw [Matrix.det_fin_two_of]; simp
  let E : SpecialLinearGroup (Fin 2) K := ⟨CE, hCEdet⟩
  let F : SpecialLinearGroup (Fin 2) K := ⟨CF, hCFdet⟩
  have hEcoe : ((E : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = CE := rfl
  have hFcoe : ((F : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = CF := rfl
  let ME : GL (Fin 5) K := ((suBlock6 (unitaryInvolution K 2 2)
    (unitaryInvolution_involutive hK) E : ↥(SU (unitaryInvolution K 2 2) 5)) :
      GL (Fin 5) K)
  let MF : GL (Fin 5) K := ((suBlock6 (unitaryInvolution K 2 2)
    (unitaryInvolution_involutive hK) F : ↥(SU (unitaryInvolution K 2 2) 5)) :
      GL (Fin 5) K)
  have hME : ((ME : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 (unitaryInvolution K 2 2) CE := by
    have := coe_suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) E
    rw [hEcoe] at this
    exact this
  have hMF : ((MF : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 (unitaryInvolution K 2 2) CF := by
    have := coe_suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) F
    rw [hFcoe] at this
    exact this
  have hEcomm : B * glAut (1 : K ≃+* K) ME * B⁻¹ = ME := hblk E
  have hFcomm : B * glAut (1 : K ≃+* K) MF * B⁻¹ = MF := hblk F
  have hEBN : B * ME = ME * B :=
    mul_eq_of_conj_eq (by simpa using hEcomm)
  have hFBN : B * MF = MF * B :=
    mul_eq_of_conj_eq (by simpa using hFcomm)
  exact ⟨ME, MF, by simpa [CE] using hME, by simpa [CF] using hMF, hEBN, hFBN⟩

theorem block_entries_of_commute_b6_blk6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {B : GL (Fin 5) K}
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut (1 : K ≃+* K) (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    (((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 0 = 0 ∧
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 1 = 0 ∧
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 0 =
        ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 1 ∧
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 3 = 0 ∧
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 3 4 = 0 ∧
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 3 3 =
        ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4) := by
  classical
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  obtain ⟨ME, MF, hME, hMF, hEBN, hFBN⟩ := block_matrices_of_commute_b6_blk6 hK hblk
  have hEmat : Bm * ((ME : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((ME : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hEBN
    simpa [Bm, Units.val_mul] using this
  have hFmat : Bm * ((MF : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((MF : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hFBN
    simpa [Bm, Units.val_mul] using this
  have hCEσ : ∀ i j, unitaryInvolution K 2 2 ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j) =
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have hCFσ : ∀ i j, unitaryInvolution K 2 2 ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j) =
      (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp
  have hXmulE := rel_block_top_fin_five (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) hME hEmat
  have hXmulF := rel_block_top_fin_five (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) hMF hFmat
  have hYmulE := rel_block_bot_fin_five (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) hCEσ hME hEmat
  have hYmulF := rel_block_bot_fin_five (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) hCFσ hMF hFmat
  obtain ⟨hX10, hX00⟩ := commute_upper_unitriangular_fin_two hXmulE
  obtain ⟨hX01, _⟩ := commute_lower_unitriangular_fin_two hXmulF
  obtain ⟨hY43, hY33⟩ := commute_upper_unitriangular_fin_two hYmulE
  obtain ⟨hY34, _⟩ := commute_lower_unitriangular_fin_two hYmulF
  exact ⟨by simpa [Bm] using hX10, by simpa [Bm] using hX01, by simpa [Bm] using hX00,
    by simpa [Bm] using hY43, by simpa [Bm] using hY34, by simpa [Bm] using hY33⟩

omit [Finite K] [CharP K 2] in
theorem offdiag_entries_of_commute_diagonal_b6 {ζ : Kˣ} (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {Bm : Matrix (Fin 5) (Fin 5) K}
    (hBmat' : Bm * diagonal (fun i => (dvec5 ζ ζ i : K)) =
      diagonal (fun i => (dvec5 ζ ζ i : K)) * Bm) :
    (Bm 0 2 = 0 ∧ Bm 0 3 = 0 ∧ Bm 0 4 = 0 ∧
      Bm 1 2 = 0 ∧ Bm 1 3 = 0 ∧ Bm 1 4 = 0 ∧
      Bm 2 0 = 0 ∧ Bm 2 1 = 0 ∧ Bm 2 3 = 0 ∧ Bm 2 4 = 0 ∧
      Bm 3 0 = 0 ∧ Bm 3 1 = 0 ∧ Bm 3 2 = 0 ∧
      Bm 4 0 = 0 ∧ Bm 4 1 = 0 ∧ Bm 4 2 = 0) := by
  have hzero : ∀ i j : Fin 5, (dvec5 ζ ζ i : K) ≠ (dvec5 ζ ζ j : K) → Bm i j = 0 :=
    fun i j hij => eq_zero_of_mul_diagonal_eq_diagonal_mul hBmat' hij
  have hζinv1 : ζ⁻¹ ≠ 1 := by
    intro hh
    apply h1
    rwa [inv_eq_one] at hh
  have h1K : (ζ : K) ≠ 1 := fun hh => h1 (Units.ext hh)
  have h1K' : (1 : K) ≠ (ζ : K) := h1K.symm
  have hζneK : (ζ : K) ≠ (ζ⁻¹ : K) := by
    intro hh
    apply hζne
    apply Units.ext
    simpa [Units.val_inv_eq_inv_val] using hh
  have hζneK' : (ζ⁻¹ : K) ≠ (ζ : K) := hζneK.symm
  have hζinvK : (ζ⁻¹ : K) ≠ 1 := by
    intro hh
    apply hζinv1
    apply Units.ext
    simpa [Units.val_inv_eq_inv_val] using hh
  have hζinvK' : (1 : K) ≠ (ζ⁻¹ : K) := hζinvK.symm
  exact ⟨hzero 0 2 (by simpa [dvec5] using h1K),
    hzero 0 3 (by simpa [dvec5] using hζneK),
    hzero 0 4 (by simpa [dvec5] using hζneK),
    hzero 1 2 (by simpa [dvec5] using h1K),
    hzero 1 3 (by simpa [dvec5] using hζneK),
    hzero 1 4 (by simpa [dvec5] using hζneK),
    hzero 2 0 (by simpa [dvec5] using h1K'),
    hzero 2 1 (by simpa [dvec5] using h1K'),
    hzero 2 3 (by simpa [dvec5] using hζinvK'),
    hzero 2 4 (by simpa [dvec5] using hζinvK'),
    hzero 3 0 (by simpa [dvec5] using hζneK'),
    hzero 3 1 (by simpa [dvec5] using hζneK'),
    hzero 3 2 (by simpa [dvec5] using hζinvK),
    hzero 4 0 (by simpa [dvec5] using hζneK'),
    hzero 4 1 (by simpa [dvec5] using hζneK'),
    hzero 4 2 (by simpa [dvec5] using hζinvK)⟩

theorem eq_diagonal_of_commute_b6_blk6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {B : GL (Fin 5) K}
    (hcomm : B * (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K))
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut (1 : K ≃+* K) (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    ∃ c : Fin 5 → K, ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal c ∧
      ∀ i, c i ≠ 0 := by
  classical
  let N : ↥(SU (unitaryInvolution K 2 2) 5) := b6 (unitaryInvolution K 2 2) ζ hζ
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  have hNgl : (N : GL (Fin 5) K) = diagU (dvec5 ζ ζ) := by
    simpa [N] using coe_b6 (unitaryInvolution K 2 2) ζ hζ
  have hBN : B * (N : GL (Fin 5) K) = (N : GL (Fin 5) K) * B := by
    calc B * (N : GL (Fin 5) K) = (B * (N : GL (Fin 5) K) * B⁻¹) * B := by group
      _ = (N : GL (Fin 5) K) * B := by rw [hcomm]
  have hBmat : Bm * ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hBN
    simpa [Bm, Units.val_mul] using this
  have hBmat' : Bm * diagonal (fun i => (dvec5 ζ ζ i : K)) =
      diagonal (fun i => (dvec5 ζ ζ i : K)) * Bm := by
    simpa [hNgl, diagU_val] using hBmat
  obtain ⟨h02, h03, h04, h12, h13, h14, h20, h21, h23, h24, h30, h31, h32, h40, h41, h42⟩ :=
    offdiag_entries_of_commute_diagonal_b6 h1 hζne hBmat'
  obtain ⟨hB10, hB01, hB00eq11, hB43, hB34, hB33eq44⟩ :=
    block_entries_of_commute_b6_blk6 hK hblk
  let c : Fin 5 → K := ![Bm 0 0, Bm 0 0, Bm 2 2, Bm 3 3, Bm 3 3]
  have hBdiag : ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = diagonal c := by
    ext i j
    change Bm i j = diagonal c i j
    fin_cases i <;> fin_cases j <;>
      simp [Bm, c, hB10, hB01, hB00eq11, hB43, hB34, hB33eq44,
        h02, h03, h04, h12, h13, h14, h20, h21, h23, h24, h30, h31, h32, h40, h41, h42]
  refine ⟨c, hBdiag, ?_⟩
  intro i hi
  apply B.det_ne_zero
  rw [hBdiag]
  exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by
    rw [Matrix.diagonal_apply]
    split_ifs with h
    · exact hi
    · rfl)

theorem diag_of_commute_b6_blk6 (hK : Nat.card K = (2 ^ 2) ^ 2)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {B : GL (Fin 5) K}
    (hcomm : B * (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K))
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut (1 : K ≃+* K) (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    B ^ 15 = 1 := by
  obtain ⟨c, hBdiag, hc0⟩ := eq_diagonal_of_commute_b6_blk6 hK hζ h1 hζne hcomm hblk
  exact pow_fifteen_of_diagonal hK hc0 hBdiag

omit [Finite K] [CharP K 2] in
theorem topRightBlock_ne_zero_of_inv {ζ : Kˣ} (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {Bm : Matrix (Fin 5) (Fin 5) K}
    (hzero : ∀ i j : Fin 5, ((dvec5 ζ ζ j : K))⁻¹ ≠ (dvec5 ζ ζ i : K) → Bm i j = 0)
    (hdet : Bm.det ≠ 0) :
    (!![Bm 0 3, Bm 0 4; Bm 1 3, Bm 1 4] : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro hP0
  have hrow0 : ∀ j, Bm 0 j = 0 := by
    intro j
    fin_cases j
    · apply hzero 0 0
      intro hh
      apply hζne
      apply Units.ext
      simpa [dvec5, Units.val_inv_eq_inv_val] using hh.symm
    · apply hzero 0 1
      intro hh
      apply hζne
      apply Units.ext
      simpa [dvec5, Units.val_inv_eq_inv_val] using hh.symm
    · apply hzero 0 2
      intro hh
      apply h1
      apply Units.ext
      simpa [dvec5] using hh.symm
    · have := congrFun (congrFun hP0 0) 0
      simpa using this
    · have := congrFun (congrFun hP0 0) 1
      simpa using this
  have hdet0 : Bm.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 0 hrow0
  exact hdet hdet0

theorem false_of_topright_relation (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (hζne : ζ ≠ ζ⁻¹)
    {φ : K ≃+* K} {B : GL (Fin 5) K} (hφζ : φ ζ = (ζ : K)⁻¹)
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K))
    (hPne : (!![((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 3,
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 0 4;
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 3,
      ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 1 4] :
        Matrix (Fin 2) (Fin 2) K) ≠ 0) : False := by
  classical
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  let Cζ : Matrix (Fin 2) (Fin 2) K := !![(ζ : K), 1; 1, 0]
  let Aζ : SpecialLinearGroup (Fin 2) K := ⟨Cζ, by simp [Cζ, CharTwo.neg_eq]⟩
  have hAζ : ((Aζ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Cζ := rfl
  have hCζ : Cζ = !![(ζ : K), 1; 1, 0] := rfl
  let M : GL (Fin 5) K := ((suBlock6 (unitaryInvolution K 2 2)
    (unitaryInvolution_involutive hK) Aζ : ↥(SU (unitaryInvolution K 2 2) 5)) :
      GL (Fin 5) K)
  have hM : ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blk6 (unitaryInvolution K 2 2) (!![(ζ : K), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    have := coe_suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) Aζ
    rw [hAζ, hCζ] at this
    exact this
  have hζcomm : B * glAut φ M * B⁻¹ = M := hblk Aζ
  have hζBN : B * glAut φ M = M * B := by
    calc B * glAut φ M = (B * glAut φ M * B⁻¹) * B := by group
      _ = M * B := by rw [hζcomm]
  have hζmat : Bm * (((glAut φ M : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hζBN
    simpa [Bm, Units.val_mul] using this
  have hrel := rel_block_topright φ (unitaryInvolution K 2 2) (ζ : K) hM hζmat
  have hφσζ : φ (unitaryInvolution K 2 2 (ζ : K)) = (ζ : K) :=
    eq_of_mul_shift_fin_two (ζ : K) (φ (unitaryInvolution K 2 2 (ζ : K)))
      (by simpa [Bm] using hPne) hrel
  rw [hζ] at hφσζ
  apply hζne
  apply Units.ext
  simpa [Units.val_inv_eq_inv_val] using (hφζ.symm.trans hφσζ).symm

theorem not_fieldAut_eq_inv (hK : Nat.card K = (2 ^ 2) ^ 2)
    {ζ : Kˣ} (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {φ : K ≃+* K} {B : GL (Fin 5) K} (hφζ : φ ζ = (ζ : K)⁻¹)
    (hcomm : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K))
    (hblk : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K)) :
    False := by
  classical
  let N : ↥(SU (unitaryInvolution K 2 2) 5) := b6 (unitaryInvolution K 2 2) ζ hζ
  let Bm : Matrix (Fin 5) (Fin 5) K := ((B : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
  have hNgl : (N : GL (Fin 5) K) = diagU (dvec5 ζ ζ) := by
    simpa [N] using coe_b6 (unitaryInvolution K 2 2) ζ hζ
  have hd2 : (dvec5 ζ ζ 2 : K) = 1 := by simp [dvec5]
  have hφN : glAut φ (N : GL (Fin 5) K) = (N : GL (Fin 5) K)⁻¹ := by
    apply Units.ext
    ext i j
    rw [coe_glAut, hNgl, diagU_val, ← diagU_inv, diagU_val]
    fin_cases i <;> fin_cases j <;>
      simp [dvec5, hφζ]
  have hcomm' : B * glAut φ (N : GL (Fin 5) K) * B⁻¹ = (N : GL (Fin 5) K) := hcomm
  have hBcomm : B * (N : GL (Fin 5) K)⁻¹ * B⁻¹ = (N : GL (Fin 5) K) := by
    rwa [hφN] at hcomm'
  have hBN : B * (N : GL (Fin 5) K)⁻¹ = (N : GL (Fin 5) K) * B := by
    calc B * (N : GL (Fin 5) K)⁻¹ =
        (B * (N : GL (Fin 5) K)⁻¹ * B⁻¹) * B := by group
      _ = (N : GL (Fin 5) K) * B := by rw [hBcomm]
  have hBmat : Bm * (((N : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) =
        ((N : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Bm := by
    have := congrArg (fun x : GL (Fin 5) K => ((x : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) hBN
    simpa [Bm, Units.val_mul] using this
  have hzero : ∀ i j : Fin 5, ((dvec5 ζ ζ j : K))⁻¹ ≠ (dvec5 ζ ζ i : K) → Bm i j = 0 := by
    intro i j hij
    have hentry := congrFun (congrFun hBmat i) j
    rw [Matrix.mul_apply, Matrix.mul_apply, hNgl, ← diagU_inv, diagU_val] at hentry
    simp [diagU_val, Matrix.diagonal_apply] at hentry
    have hkey : Bm i j * (((dvec5 ζ ζ j : K))⁻¹ - (dvec5 ζ ζ i : K)) = 0 := by
      linear_combination hentry
    rcases mul_eq_zero.1 hkey with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hij
  have hPne : (!![Bm 0 3, Bm 0 4; Bm 1 3, Bm 1 4] : Matrix (Fin 2) (Fin 2) K) ≠ 0 :=
    topRightBlock_ne_zero_of_inv h1 hζne hzero B.det_ne_zero
  exact false_of_topright_relation hK hζ hζne hφζ hblk (by simpa [Bm] using hPne)


noncomputable def suQStated (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ↥(SU (unitaryInvolution K 2 2) 5) →* StatedProj (StatedSU 5 (2 ^ 2) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K))).comp
    (suToStated hK 5).toMonoidHom

theorem eq_scalar_mul_of_fix_suQStated (hK : Nat.card K = (2 ^ 2) ^ 2)
    {φ : K ≃+* K} {A : GL (Fin 5) K}
    {γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))}
    (hγ : ∀ g : StatedSU 5 (2 ^ 2) K,
      ∃ hg : A * glAut φ (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
        γ (QuotientGroup.mk g) =
          QuotientGroup.mk ⟨A * glAut φ (g : GL (Fin 5) K) * A⁻¹, hg⟩)
    {g : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hgfix : γ (suQStated hK g) = suQStated hK g) :
    ∃ u : Kˣ, ((g : GL (Fin 5) K)) =
      (((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5)) *
        glAut φ (g : GL (Fin 5) K) *
          ((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5))⁻¹ : GL (Fin 5) K) *
        GeneralLinearGroup.scalar (Fin 5) u := by
  let N : Subgroup (StatedSU 5 (2 ^ 2) K) :=
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)
  set P : GL (Fin 5) K := wittMat hK 5 with hP
  set B : GL (Fin 5) K := P⁻¹ * A * glAut φ P with hB
  obtain ⟨hg, hform⟩ := hγ (suToStated hK 5 g)
  have hform' : γ ((QuotientGroup.mk' N) (suToStated hK 5 g)) =
      (QuotientGroup.mk' N) ⟨A * glAut φ ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) :
        GL (Fin 5) K) * A⁻¹, hg⟩ := hform
  have hfix' : γ ((QuotientGroup.mk' N) (suToStated hK 5 g)) =
      (QuotientGroup.mk' N) (suToStated hK 5 g) := hgfix
  have h1 : (QuotientGroup.mk' N) ⟨A * glAut φ ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) :
        GL (Fin 5) K) * A⁻¹, hg⟩ =
      (QuotientGroup.mk' N) (suToStated hK 5 g) := by
    rw [← hform']
    exact hfix'
  obtain ⟨u, hu⟩ := (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (StatedSU 5 (2 ^ 2) K)
    ⟨A * glAut φ ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) : GL (Fin 5) K) * A⁻¹, hg⟩
    (suToStated hK 5 g)).1 h1
  have hψ : ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) : GL (Fin 5) K) =
      P * (g : GL (Fin 5) K) * P⁻¹ := coe_suToStated hK 5 g
  have hM : (A * glAut φ ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) : GL (Fin 5) K) *
        A⁻¹ : GL (Fin 5) K) = P * (B * glAut φ (g : GL (Fin 5) K) * B⁻¹) * P⁻¹ := by
    rw [hψ]
    simp only [map_mul, map_inv]
    simp [hB]
    group
  have hscalar : ((GeneralLinearGroup.scalar (Fin 5) u : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = (u : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    ext i j
    by_cases h : i = j <;> simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, h]
  have huGL : ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) : GL (Fin 5) K) =
      (A * glAut φ ((suToStated hK 5 g : StatedSU 5 (2 ^ 2) K) : GL (Fin 5) K) * A⁻¹ :
        GL (Fin 5) K) * GeneralLinearGroup.scalar (Fin 5) u := by
    apply Units.ext
    rw [Units.val_mul, hscalar]
    exact hu
  rw [hM, hψ] at huGL
  have hP : P⁻¹ * (P * (g : GL (Fin 5) K) * P⁻¹) * P = (g : GL (Fin 5) K) := by group
  have hPs : P⁻¹ * GeneralLinearGroup.scalar (Fin 5) u * P =
      GeneralLinearGroup.scalar (Fin 5) u := by
    rw [mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcancel : (g : GL (Fin 5) K) = (B * glAut φ (g : GL (Fin 5) K) * B⁻¹) *
      GeneralLinearGroup.scalar (Fin 5) u := by
    have := congrArg (fun x : GL (Fin 5) K => P⁻¹ * x * P) huGL
    simpa [mul_assoc, hP, hPs] using this
  exact ⟨u, by simpa [B, P] using hcancel⟩

theorem exists_unit_of_fix_suQStated (hK : Nat.card K = (2 ^ 2) ^ 2)
    {φ : K ≃+* K} {A : GL (Fin 5) K}
    {γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))}
    (hγ : ∀ g : StatedSU 5 (2 ^ 2) K,
      ∃ hg : A * glAut φ (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
        γ (QuotientGroup.mk g) =
          QuotientGroup.mk ⟨A * glAut φ (g : GL (Fin 5) K) * A⁻¹, hg⟩)
    {g : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hgfix : γ (suQStated hK g) = suQStated hK g) :
    ∃ u : Kˣ, (((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5)) *
        glAut φ (g : GL (Fin 5) K) *
          ((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5))⁻¹ : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) u * (g : GL (Fin 5) K) := by
  obtain ⟨u, hu⟩ := eq_scalar_mul_of_fix_suQStated hK hγ hgfix
  let X : GL (Fin 5) K :=
    ((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5)) * glAut φ (g : GL (Fin 5) K) *
      ((wittMat hK 5)⁻¹ * A * glAut φ (wittMat hK 5))⁻¹
  have hcancel' : (g : GL (Fin 5) K) = X * GeneralLinearGroup.scalar (Fin 5) u := by
    simpa [X] using hu
  refine ⟨u⁻¹, ?_⟩
  change X = GeneralLinearGroup.scalar (Fin 5) u⁻¹ * (g : GL (Fin 5) K)
  conv_rhs => rw [hcancel']
  rw [(GeneralLinearGroup.scalar_commute u X).symm]
  rw [← mul_assoc, ← map_mul]
  simp

omit [Finite K] [CharP K 2] in
theorem zeta_sq_ne_one_of_cube {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) :
    ζ ^ 2 ≠ 1 := by
  intro hζ2
  apply h1
  have h3' := h3
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hζ2, one_mul] at h3'
  exact h3'

omit [Finite K] in
theorem fieldAut_zeta_eq_zeta_or_inv {ζ : Kˣ} (h1 : ζ ≠ 1) (h2 : ζ ^ 2 ≠ 1)
    (h3 : ζ ^ 3 = 1) (φ : K ≃+* K) :
    ζ ≠ ζ⁻¹ ∧ (φ ζ = ζ ∨ φ ζ = (ζ : K)⁻¹) := by
  have hζne : ζ ≠ ζ⁻¹ := by
    intro hh
    apply h2
    calc ζ ^ 2 = ζ * ζ := by rw [pow_two]
      _ = ζ * ζ⁻¹ := congrArg (fun x => ζ * x) hh
      _ = 1 := mul_inv_cancel ζ
  have h3K : (ζ : K) ^ 3 = 1 := by
    simpa using congrArg (fun x : Kˣ => (x : K)) h3
  have hζ0 : (ζ : K) ≠ 0 := by
    intro hz
    have h : (ζ : K) * (ζ : K) ^ 2 = 1 := by
      rw [← pow_succ', show 1 + 2 = 3 by norm_num]
      simpa using h3K
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have h1K : (ζ : K) ≠ 1 := fun h => h1 (Units.ext h)
  have hζ2 : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have hfac : (ζ : K) ^ 3 - 1 = (ζ - 1) * (ζ ^ 2 + ζ + 1) := by ring
    have h : ((ζ : K) - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
      rw [← hfac, h3K, sub_self]
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) h1K
    · exact h
  have hζ2' : (ζ : K) ^ 2 + 1 = ζ := by
    calc (ζ : K) ^ 2 + 1 = (ζ : K) ^ 2 + 1 + (ζ + ζ) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
      _ = ((ζ : K) ^ 2 + ζ + 1) + ζ := by abel
      _ = ζ := by rw [hζ2, zero_add]
  have hsum : (ζ : K) + (ζ : K)⁻¹ = 1 := by
    field_simp [hζ0]
    linear_combination hζ2'
  have hroot : (φ ζ) ^ 2 + φ ζ + 1 = 0 := by
    have h := congrArg φ hζ2
    simpa [map_add, map_pow, map_one, map_zero] using h
  have hfac : ((φ ζ : K) - ζ) * ((φ ζ : K) - (ζ : K)⁻¹) = 0 := by
    have hexp : ((φ ζ : K) - ζ) * ((φ ζ : K) - (ζ : K)⁻¹) =
        (φ ζ) ^ 2 + ((ζ : K) + (ζ : K)⁻¹) * (φ ζ) + 1 := by
      rw [sub_eq_add_neg, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.neg_eq]
      ring_nf
      rw [mul_inv_cancel₀ hζ0]
      ring
    rw [hexp, hsum, one_mul, hroot]
  have hφζ : φ ζ = ζ ∨ φ ζ = (ζ : K)⁻¹ := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  exact ⟨hζne, hφζ⟩

omit [Finite K] [CharP K 2] in
theorem pow_apply_of_normal_form
    {γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))} {A : GL (Fin 5) K}
    (hγnf1 : ∀ g : StatedSU 5 (2 ^ 2) K,
        ∃ hg : A * (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
          γ (QuotientGroup.mk g) =
            QuotientGroup.mk ⟨A * (g : GL (Fin 5) K) * A⁻¹, hg⟩) :
    ∀ m : ℕ, ∀ g : StatedSU 5 (2 ^ 2) K,
      ∃ hg : A ^ m * (g : GL (Fin 5) K) * (A ^ m)⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
        (γ ^ m) (QuotientGroup.mk g) =
          QuotientGroup.mk ⟨A ^ m * (g : GL (Fin 5) K) * (A ^ m)⁻¹, hg⟩ := by
  intro m
  induction m with
  | zero =>
      intro g
      exact ⟨by simp, by simp⟩
  | succ m ih =>
      intro g
      obtain ⟨hg, hgm⟩ := ih g
      let g' : StatedSU 5 (2 ^ 2) K :=
        ⟨A ^ m * (g : GL (Fin 5) K) * (A ^ m)⁻¹, hg⟩
      obtain ⟨hg', hg'eq⟩ := hγnf1 g'
      refine ⟨?_, ?_⟩
      · have heq : A ^ (m + 1) * (g : GL (Fin 5) K) * (A ^ (m + 1))⁻¹ =
            A * (g' : GL (Fin 5) K) * A⁻¹ := by
          simp [g', pow_succ]
          group
        rwa [heq]
      · have hstep : (γ ^ (m + 1)) (QuotientGroup.mk g) =
            γ ((γ ^ m) (QuotientGroup.mk g)) := by
          simp [pow_succ']
        rw [hstep, hgm, hg'eq]
        congr 1
        apply Subtype.ext
        simp [g', pow_succ]
        group

omit [Finite K] [CharP K 2] in
theorem pow_fifteen_of_normal_form
    {γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))} {A : GL (Fin 5) K}
    (hγnf1 : ∀ g : StatedSU 5 (2 ^ 2) K,
        ∃ hg : A * (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
          γ (QuotientGroup.mk g) =
            QuotientGroup.mk ⟨A * (g : GL (Fin 5) K) * A⁻¹, hg⟩)
    (hA15 : A ^ 15 = 1) (hγ : ∃ k : ℕ, γ ^ 2 ^ k = 1) : γ = 1 := by
  have hpow := pow_apply_of_normal_form hγnf1
  have hγ15 : γ ^ 15 = 1 := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)) x
    obtain ⟨hg, hgm⟩ := hpow 15 g
    change (γ ^ 15) (QuotientGroup.mk g) = QuotientGroup.mk g
    calc (γ ^ 15) (QuotientGroup.mk g)
        = QuotientGroup.mk ⟨A ^ 15 * (g : GL (Fin 5) K) * (A ^ 15)⁻¹, hg⟩ := hgm
      _ = QuotientGroup.mk g := by
          have hA : A ^ 15 * (g : GL (Fin 5) K) * (A ^ 15)⁻¹ = (g : GL (Fin 5) K) := by
            rw [hA15]
            group
          congr 1
          apply Subtype.ext
          exact hA
  obtain ⟨k, hk⟩ := hγ
  have hcop : Nat.Coprime 15 (2 ^ k) := (by norm_num : Nat.Coprime 15 2).pow_right k
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hγ15, hk⟩

theorem eq_one_of_fix_suQStated_of_fieldAut_eq (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (hζne : ζ ≠ ζ⁻¹)
    {γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))}
    {φ : K ≃+* K} {P A B : GL (Fin 5) K} (hφz : φ ζ = ζ)
    (hcommb : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K))
    (hLA : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K))
    (hγnf : ∀ g : StatedSU 5 (2 ^ 2) K,
      ∃ hg : A * glAut φ (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
        γ (QuotientGroup.mk g) =
          QuotientGroup.mk ⟨A * glAut φ (g : GL (Fin 5) K) * A⁻¹, hg⟩)
    (hγ : ∃ k : ℕ, γ ^ 2 ^ k = 1)
    (hBdef : B = P⁻¹ * A * glAut φ P) : γ = 1 := by
  have hφ1 : φ = 1 :=
    fieldAut_eq_one_of_commute_b6_blk6 hK hζ h1 hζne hφz hcommb hLA
  have hB15 : B ^ 15 = 1 :=
    diag_of_commute_b6_blk6 hK hζ h1 hζne (by simpa [hφ1] using hcommb)
      (by simpa [hφ1] using hLA)
  have hBdefP : B = P⁻¹ * A * P := by
    rw [hBdef, hφ1]
    simp
  have hAeq : A = P * B * P⁻¹ := by
    rw [hBdefP]
    group
  have hA15 : A ^ 15 = 1 := by
    rw [hAeq]
    calc (P * B * P⁻¹) ^ 15 = P * B ^ 15 * P⁻¹ := by
          simp
      _ = 1 := by rw [hB15]; group
  have hγnf1 : ∀ g : StatedSU 5 (2 ^ 2) K,
      ∃ hg : A * (g : GL (Fin 5) K) * A⁻¹ ∈ StatedSU 5 (2 ^ 2) K,
        γ (QuotientGroup.mk g) =
          QuotientGroup.mk ⟨A * (g : GL (Fin 5) K) * A⁻¹, hg⟩ := by
    intro g
    obtain ⟨hg, hg'⟩ := hγnf g
    exact ⟨by simpa [hφ1] using hg, by simpa [hφ1] using hg'⟩
  exact pow_fifteen_of_normal_form hγnf1 hA15 hγ

theorem eq_one_of_fix_suQStated_b6_suBlock6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (γ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)))
    (hγ : ∃ k : ℕ, γ ^ 2 ^ k = 1)
    (hb : γ (suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ)) =
      suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ))
    (hL : ∀ A : SpecialLinearGroup (Fin 2) K,
      γ (suQStated hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)) =
        suQStated hK (suBlock6 (unitaryInvolution K 2 2)
          (unitaryInvolution_involutive hK) A)) :
    γ = 1 := by
  classical
  have h : UnitaryFieldData 2 2 K :=
    { prime := Nat.prime_two, one_le := by norm_num, card := by rw [hK]; norm_num }
  obtain ⟨φ, A, hA, hγnf⟩ :=
    exists_unitary_semilinear_statedProj h (n := 5) (by norm_num) (by norm_num) γ
  let P : GL (Fin 5) K := wittMat hK 5
  let B : GL (Fin 5) K := P⁻¹ * A * glAut φ P
  obtain ⟨u_b, hu_b⟩ := exists_unit_of_fix_suQStated hK hγnf hb
  have hub : u_b = 1 := eq_one_of_conj_smul_b6 hζ h1 h3 hu_b
  have hcommb : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹ =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) := by
    simpa [B, hub] using hu_b
  have hBN : B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) =
      (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B := by
    calc B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) =
        (B * glAut φ (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B⁻¹) * B := by
          group
      _ = (b6 (unitaryInvolution K 2 2) ζ hζ : GL (Fin 5) K) * B := by rw [hcommb]
  have h2 : ζ ^ 2 ≠ 1 := zeta_sq_ne_one_of_cube h1 h3
  obtain ⟨a, ha, hBe⟩ := exists_smul_single_of_conj_b6 hζ h1 h2 hBN
  have hLA : ∀ A : SpecialLinearGroup (Fin 2) K,
      B * glAut φ (((suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A : ↥(SU (unitaryInvolution K 2 2) 5)) :
          GL (Fin 5) K)) * B⁻¹ =
        ((suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) := by
    intro A
    obtain ⟨u, hu⟩ := exists_unit_of_fix_suQStated hK hγnf (hL A)
    have hu1 : u = 1 :=
      eq_one_of_conj_smul_of_fix (e := Pi.single 2 (1 : K)) rfl ha hBe
        (mulVec_single_two_glAut_suBlock6 hK φ A) (mulVec_single_two_suBlock6 hK A) hu
    simpa [B, hu1] using hu
  obtain ⟨hζne, hφζ⟩ := fieldAut_zeta_eq_zeta_or_inv h1 h2 h3 φ
  rcases hφζ with hφz | hφz
  · exact eq_one_of_fix_suQStated_of_fieldAut_eq hK hζ h1 hζne hφz hcommb hLA hγnf hγ
      (show B = P⁻¹ * A * glAut φ P from rfl)
  · exact (not_fieldAut_eq_inv hK hζ h1 hζne hφz hcommb hLA).elim

theorem ker_suQ_eq_ker_suQStated (hK : Nat.card K = (2 ^ 2) ^ 2) :
    (suQStated hK).ker = (suQ 5 hK).ker := by
  classical
  let H : Subgroup (GL (Fin 5) K) := StatedSU 5 (2 ^ 2) K
  let N : Subgroup H := (StatedScalars (Fin 5) K).subgroupOf H
  have hcenter : Subgroup.center H = N :=
    (isQuasisimple_statedSU_of_card (p := 2) (f := 2) hK (by norm_num) (by norm_num)).2
  have hker_suQ : (suQ 5 hK).ker = N.comap (equivStatedSU hK 5).toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hker_q : (suQStated hK).ker = N.comap (suToStated hK 5).toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hcomap : ∀ (e : ↥(SU (unitaryInvolution K 2 2) 5) ≃* H),
      N.comap e.toMonoidHom = Subgroup.center (SU (unitaryInvolution K 2 2) 5) := by
    intro e
    have hmap := map_center_mulEquiv e
    rw [hcenter] at hmap
    ext g
    rw [Subgroup.mem_comap, ← hmap, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hye⟩
      rwa [e.injective hye] at hy
    · intro hg
      exact ⟨g, hg, rfl⟩
  rw [hker_suQ, hker_q, hcomap (equivStatedSU hK 5), hcomap (suToStated hK 5)]

theorem exists_mulAut_suQ_eq_suQStated (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ δ : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K)),
      ∀ g : ↥(SU (unitaryInvolution K 2 2) 5), δ (suQStated hK g) = suQ 5 hK g := by
  classical
  let H : Subgroup (GL (Fin 5) K) := StatedSU 5 (2 ^ 2) K
  let N : Subgroup H := (StatedScalars (Fin 5) K).subgroupOf H
  let PSU : Type := StatedProj H
  have hker : (suQStated hK).ker = (suQ 5 hK).ker := ker_suQ_eq_ker_suQStated hK
  have hsurj : Function.Surjective (suQ 5 hK) :=
    (QuotientGroup.mk'_surjective N).comp (equivStatedSU hK 5).surjective
  have hsurj' : Function.Surjective (suQStated hK) :=
    (QuotientGroup.mk'_surjective N).comp (suToStated hK 5).surjective
  let e : (↥(SU (unitaryInvolution K 2 2) 5) ⧸ (suQ 5 hK).ker) ≃* PSU :=
    QuotientGroup.quotientKerEquivOfSurjective (suQ 5 hK) hsurj
  let e' : (↥(SU (unitaryInvolution K 2 2) 5) ⧸ (suQStated hK).ker) ≃* PSU :=
    QuotientGroup.quotientKerEquivOfSurjective (suQStated hK) hsurj'
  let δ : MulAut PSU :=
    (e'.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans e))
  have hδ : ∀ g : ↥(SU (unitaryInvolution K 2 2) 5),
      δ (suQStated hK g) = suQ 5 hK g := by
    intro g
    show e (QuotientGroup.quotientMulEquivOfEq hker (e'.symm (suQStated hK g))) =
      suQ 5 hK g
    have h1 : e'.symm (suQStated hK g) = QuotientGroup.mk g := by
      apply e'.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  exact ⟨δ, hδ⟩

theorem eq_one_of_fix_suBlock6_b6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    (β : MulAut (StatedProj (StatedSU 5 (2 ^ 2) K))) (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1)
    (hb : β (suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ)) =
      suQ 5 hK (b6 (unitaryInvolution K 2 2) ζ hζ))
    (hL : ∀ A : SpecialLinearGroup (Fin 2) K,
      β (suQ 5 hK (suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A)) =
        suQ 5 hK (suBlock6 (unitaryInvolution K 2 2) (unitaryInvolution_involutive hK) A)) :
    β = 1 := by
  let PSU : Type := StatedProj (StatedSU 5 (2 ^ 2) K)
  obtain ⟨δ, hδ⟩ := exists_mulAut_suQ_eq_suQStated hK
  let γ : MulAut PSU := δ.symm * β * δ
  have hγorder : ∃ k : ℕ, γ ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hβ
    refine ⟨k, ?_⟩
    have hconj : γ ^ 2 ^ k = δ.symm * β ^ 2 ^ k * δ := by
      simpa [γ] using conj_pow (a := (δ.symm : MulAut PSU)) (b := β) (i := 2 ^ k)
    rw [hconj, hk]
    change δ⁻¹ * δ = 1
    exact inv_mul_cancel δ
  have hb' : γ (suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ)) =
      suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ) := by
    show δ.symm (β (δ (suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ)))) =
      suQStated hK (b6 (unitaryInvolution K 2 2) ζ hζ)
    rw [hδ, hb, ← hδ, MulEquiv.symm_apply_apply]
  have hL' : ∀ A : SpecialLinearGroup (Fin 2) K,
      γ (suQStated hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)) =
        suQStated hK (suBlock6 (unitaryInvolution K 2 2)
          (unitaryInvolution_involutive hK) A) := by
    intro A
    show δ.symm (β (δ (suQStated hK (suBlock6 (unitaryInvolution K 2 2)
      (unitaryInvolution_involutive hK) A)))) =
      suQStated hK (suBlock6 (unitaryInvolution K 2 2)
        (unitaryInvolution_involutive hK) A)
    rw [hδ, hL A, ← hδ, MulEquiv.symm_apply_apply]
  have hγ1 : γ = 1 := eq_one_of_fix_suQStated_b6_suBlock6 hK hζ h1 h3 γ hγorder hb' hL'
  have hβeq : δ * γ * δ.symm = β := by
    change δ * (δ⁻¹ * β * δ) * δ⁻¹ = β
    group
  rw [← hβeq, hγ1]
  change δ * δ⁻¹ = 1
  exact mul_inv_cancel δ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.AutOdd

end
