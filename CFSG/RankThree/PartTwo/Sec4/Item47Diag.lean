module

public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open Matrix

section PSL2

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {K : Type*} [Field K]

theorem det_coe_scalar {n : ℕ} (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (c : K) ^ n := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem det_pow_mul_scalar_inv {n : ℕ} (A : GL (Fin n) K) :
    (((A ^ n * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det A)⁻¹ : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [Units.val_mul, Matrix.det_mul, det_coe_scalar, Units.val_pow_eq_pow_val, Matrix.det_pow,
    ← GeneralLinearGroup.val_det_apply, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    ← Units.val_mul, inv_pow, mul_inv_cancel, Units.val_one]

theorem isInnerAut_pglAction_sq (g : PGL2 K) : IsInnerAut (pglAction K g ^ 2) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
  set d : Kˣ := GeneralLinearGroup.det A
  let B : SpecialLinearGroup (Fin 2) K :=
    ⟨((A ^ 2 * GeneralLinearGroup.scalar (Fin 2) d⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
      det_pow_mul_scalar_inv A⟩
  refine ⟨(B : PSL2 K), ?_⟩
  rw [← pglAction_toPGL, ← map_pow, ProjectiveSpecialLinearGroup.toPGL_mk, ← map_pow]
  congr 1
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  have hB : SpecialLinearGroup.toGL B = A ^ 2 * GeneralLinearGroup.scalar (Fin 2) d⁻¹ :=
    Units.ext rfl
  refine ⟨d, ?_⟩
  rw [hB, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

theorem psl2_inndiag_cube : ∀ τ ∈ (stdPinnedPSL2 K).inndiag, τ ^ 3 = 1 → IsInnerAut τ := by
  rintro _ ⟨g, rfl⟩ h3
  exact isInnerAut_of_pow_three_eq_one h3 (by norm_num) (isInnerAut_pglAction_sq g)

end PSL2

section PSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {K : Type*} [Field K]

theorem isInnerAut_conjAut_of_det (A : GL (Fin n) K) (hA : (A : Matrix (Fin n) (Fin n) K).det = 1) :
    IsInnerAut (conjAut n K A) :=
  conjAut_mem_range_conj_of_det_eq_pow (μ := 1) (by rw [one_pow]; exact Units.ext hA)

theorem isInnerAut_conjAut_pow_n (A : GL (Fin n) K) : IsInnerAut (conjAut n K A ^ n) :=
  pow_mem_range_conj_of_mem_linearAutGroup (conjAut_mem_linearAutGroup A)

theorem isInnerAut_conjAut_pow_card_units [Finite K] (A : GL (Fin n) K) :
    IsInnerAut (conjAut n K A ^ Nat.card Kˣ) := by
  rw [← map_pow]
  apply isInnerAut_conjAut_of_det
  rw [Units.val_pow_eq_pow_val, Matrix.det_pow, ← GeneralLinearGroup.val_det_apply,
    ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one]

theorem psl_inndiag_cube [Finite K] (hcop : ¬ 3 ∣ n ∨ ¬ 3 ∣ Nat.card Kˣ) :
    ∀ τ ∈ (stdPinnedPSL n K).inndiag, τ ^ 3 = 1 → IsInnerAut τ := by
  intro τ hτ h3
  rw [stdPinnedPSL_inndiag, mem_linearAutGroup_iff] at hτ
  obtain ⟨A, rfl⟩ := hτ
  rcases hcop with h | h
  · exact isInnerAut_of_pow_three_eq_one h3 h (isInnerAut_conjAut_pow_n A)
  · exact isInnerAut_of_pow_three_eq_one h3 h (isInnerAut_conjAut_pow_card_units A)

end PSL

section PSU

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem det_pow_succ_eq_one {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    (A : Matrix (Fin 3) (Fin 3) K).det ^ (p ^ f + 1) = 1 := by
  have h1 := CFSG.RankThree.PartTwo.KFacts.norm_det_of_mem_unitaryIsom3 hA
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, mul_comm] at h1
  rwa [pow_succ]

theorem isInnerAut_psuConj_pow (A : unitaryIsom3 h) :
    IsInnerAut (psuConj h A ^ (p ^ f + 1)) := by
  rw [← map_pow]
  have hmem : ((A ^ (p ^ f + 1) : unitaryIsom3 h) : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, (A ^ (p ^ f + 1)).2⟩
    rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, Matrix.det_pow, det_pow_succ_eq_one A.2]
  refine ⟨((⟨_, hmem⟩ : unitarySU p f K 3) : unitaryPSU h 3), ?_⟩
  rw [conj_mk_eq_psuConj]

theorem psu3_inndiag_cube (hcop : ¬ 3 ∣ p ^ f + 1) :
    ∀ τ ∈ (stdPinnedPSU3 h).inndiag, τ ^ 3 = 1 → IsInnerAut τ := by
  rintro _ ⟨A, rfl⟩ h3
  exact isInnerAut_of_pow_three_eq_one h3 hcop (isInnerAut_psuConj_pow A)

end PSU

section PSp

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K]

theorem isInnerAut_spConjAut_sq (A : gsp r K) : IsInnerAut (conjAut r K A ^ 2) := by
  obtain ⟨μ, hμ⟩ := A.2
  set B : GL (Fin r ⊕ Fin r) K :=
    GeneralLinearGroup.scalar (Fin r ⊕ Fin r) μ⁻¹ * ((A : GL (Fin r ⊕ Fin r) K) ^ 2) with hB
  have hBsp : B ∈ StatedSp r K := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    have hA2 : ((((A : GL (Fin r ⊕ Fin r) K) ^ 2 : GL (Fin r ⊕ Fin r) K)) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
          (((A : GL (Fin r ⊕ Fin r) K) ^ 2 : GL (Fin r ⊕ Fin r) K) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = ((μ * μ : Kˣ) : K) • formJ r K := by
      rw [pow_two, Units.val_mul, mul_transpose_formJ_mul hμ, hμ, smul_smul, Units.val_mul]
    have hsc : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) μ⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = ((μ⁻¹ : Kˣ) : K) • 1 := by
      rw [GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
      rfl
    change ((B : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((B : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = formJ r K
    rw [hB, Units.val_mul, hsc, Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hA2, smul_smul]
    have : ((μ⁻¹ : Kˣ) : K) * ((μ⁻¹ : Kˣ) : K) * ((μ * μ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul]
      have : μ⁻¹ * μ⁻¹ * (μ * μ) = 1 := by group
      rw [this, Units.val_one]
    rw [this, one_smul]
  have hdecomp : (A ^ 2 : gsp r K) =
      ⟨_, scalar_mem_gsp μ⟩ * ⟨B, statedSp_le_gsp hBsp⟩ := by
    apply Subtype.ext
    change (A : GL (Fin r ⊕ Fin r) K) ^ 2 = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) μ * B
    rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨proj r K ⟨B, hBsp⟩, ?_⟩
  rw [conj_proj_eq_spConjAut, ← map_pow, hdecomp, map_mul, conjAut_scalar_eq_one, one_mul]

theorem psp_inndiag_cube : ∀ τ ∈ (stdPinnedPSp r K).inndiag, τ ^ 3 = 1 → IsInnerAut τ := by
  rintro _ ⟨A, rfl⟩ h3
  exact isInnerAut_of_pow_three_eq_one h3 (by norm_num) (isInnerAut_spConjAut_sq A)

theorem psp4Even_inndiag_cube {F : Type} [Field F] [Finite F] [CharP F 2] :
    ∀ τ ∈ (stdPinnedPSp4Even F).inndiag, τ ^ 3 = 1 → IsInnerAut τ := by
  rintro _ ⟨A, rfl⟩ h3
  exact isInnerAut_of_pow_three_eq_one h3 (by norm_num) (isInnerAut_spConjAut_sq A)

end PSp

end CFSG.RankThree.PartTwo.Sec4
