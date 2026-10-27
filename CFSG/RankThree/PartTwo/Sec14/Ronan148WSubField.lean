module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

section Linear

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts

@[expose] noncomputable def transvSL : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection 0 1 1, Matrix.det_transvection_of_ne 0 1 (by decide) 1⟩

theorem coe_transvSL :
    ((transvSL : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.transvection 0 1 1 :=
  rfl

theorem map_transvSL (σ : K ≃+* K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) =
      transvSL := by
  apply Subtype.ext
  change (Matrix.transvection (0 : Fin 3) 1 (1 : K)).map σ = Matrix.transvection 0 1 1
  ext i j
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

theorem transvSL_sq (h2 : (2 : K) = 0) :
    (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) ^ 2 = 1 := by
  have hm : Matrix.transvection (0 : Fin 3) 1 (1 : K) * Matrix.transvection 0 1 1 = 1 := by
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    rw [Matrix.transvection_mul_transvection_same 0 1 h01, one_add_one_eq_two, h2,
      Matrix.transvection_zero]
  have h1 : ((transvSL ^ 2 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((1 : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, sq, coe_transvSL, hm]
  exact Subtype.ext h1

theorem transvSL_not_mem_statedScalars (H : GL (Fin 3) K) :
    H * Matrix.SpecialLinearGroup.toGL (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) * H⁻¹ ∉
      StatedScalars (Fin 3) K := by
  rintro ⟨c, hc⟩
  have h1 : Matrix.SpecialLinearGroup.toGL (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    have e1 : Matrix.SpecialLinearGroup.toGL (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) =
        H⁻¹ * GeneralLinearGroup.scalar (Fin 3) c * H := by
      rw [hc]
      group
    rw [e1, mul_assoc, ← commute_of_mem_statedScalars ⟨c, rfl⟩ H, inv_mul_cancel_left]
  have h01 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) h1
  have e2 : ((Matrix.SpecialLinearGroup.toGL (transvSL : Matrix.SpecialLinearGroup (Fin 3) K) :
      GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
    change Matrix.transvection (0 : Fin 3) 1 (1 : K) 0 1 = 1
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  have e3 : ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  simp only [e2, e3] at h01
  exact one_ne_zero h01

theorem aut_pgl_or_fix_linear (hK : PiField true p f K) (hp : p = 2 ∨ f ≤ 2)
    (α : MulAut (projImage (slPi true 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi true 3 (p ^ f) K, ∀ m : projImage (slPi true 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) ∨
    ∃ m : projImage (slPi true 3 (p ^ f) K), m ≠ 1 ∧ m ^ p = 1 ∧ α m = m := by
  have := hK.finite
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set α' := MulAut.congr ψ α with hα'
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow, hα3, map_one]
  have hproj : ∀ t : Matrix.SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hcoe : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K,
      α (slToPsl (p ^ f) K s) = ψ.symm (α' (proj 3 K s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj,
      MulEquiv.symm_apply_apply]
  by_cases hD : α' ∈ linearAutGroup 3 K
  · left
    obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hD
    refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (p ^ f) m
    rw [hcoe, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl, toGL_slConjugation, map_mul,
      map_mul, map_inv]
  · right
    obtain ⟨σ, hσ3, H, hαH⟩ := linear_order_three_field_descent le_rfl α' hα'3 hD
    obtain ⟨h3f, -⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime hK.one_le
      (hK.card : Nat.card K = p ^ f) hσ3
    have hp2 : p = 2 := hp.resolve_right (by
      obtain ⟨f₀, hf₀⟩ := h3f
      have := hK.one_le
      omega)
    subst hp2
    have : CharP K 2 := hK.charP
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hfix : α' (conjAut 3 K H (proj 3 K transvSL)) = conjAut 3 K H (proj 3 K transvSL) := by
      rw [hαH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, fieldAut_proj,
        map_transvSL]
    refine ⟨ψ.symm (conjAut 3 K H (proj 3 K transvSL)), ?_, ?_, ?_⟩
    · rw [conjAut_proj, hproj]
      intro h1
      have h2' := congrArg (fun m : projImage (slPi true 3 (2 ^ f) K) =>
        (m : ProjGenLinGroup (Fin 3) K)) h1
      simp only [coe_slToPsl, toGL_slConjugation, Subgroup.coe_one] at h2'
      exact transvSL_not_mem_statedScalars H (mk_eq_one_iff_mem_statedScalars.mp h2')
    · rw [← map_pow, ← map_pow, ← map_pow, transvSL_sq h2, map_one, map_one, map_one]
    · have h1 : α (ψ.symm (conjAut 3 K H (proj 3 K transvSL))) =
          ψ.symm (α' (conjAut 3 K H (proj 3 K transvSL))) := by
        rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [h1, hfix]

end Linear

section Unitary

variable {K : Type} [Field K] {p f : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

@[expose] def swapMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem swapMat_mul_self : (swapMat : Matrix (Fin 3) (Fin 3) K) * swapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swapGL : GL (Fin 3) K := ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

theorem coe_swapGL : ((swapGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = swapMat :=
  rfl

theorem swapMat_map {F : Type*} [FunLike F K K] [RingHomClass F K K] (σ : F) :
    (swapMat : Matrix (Fin 3) (Fin 3) K).map σ = swapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

theorem swapGL_mem_unitarySU (h : UnitaryFieldData p f K) (h2 : (2 : K) = 0) :
    (swapGL : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h, coe_swapGL, swapMat_map h.bar]
  refine ⟨?_, ?_⟩
  · rw [swapMat, Matrix.det_fin_three]
    simp
    linear_combination -h2
  · have ht : (swapMat : Matrix (Fin 3) (Fin 3) K)ᵀ = swapMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapMat]
    rw [ht, swapMat_mul_self]

theorem aut_pgl_or_fix_unitary (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    (hp : p = 2 ∨ f ≤ 2) (α : MulAut (projImage (slPi false 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi false 3 (p ^ f) K, ∀ m : projImage (slPi false 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) ∨
    ∃ m : projImage (slPi false 3 (p ^ f) K), m ≠ 1 ∧ m ^ p = 1 ∧ α m = m := by
  have h := hK.unitary
  have := hK.finite
  set ψ := psuEquivUnitary h with hψ
  set α' := MulAut.congr ψ α with hα'
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', ← map_pow, hα3, map_one]
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hcoe : ∀ s : unitarySU p f K 3,
      α (suToPsu p f K s) = ψ.symm (α' (unitaryProj h 3 s)) := by
    intro s
    rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj,
      MulEquiv.symm_apply_apply]
  by_cases hD : α' ∈ (psuConj h).range
  · left
    obtain ⟨A, hA⟩ := hD
    refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := suToPsu_surjective (p := p) (f := f) (K := K) m
    rw [hcoe, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, coe_suConj, map_mul,
      map_mul, Subgroup.coe_inv, map_inv]
  · right
    obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 α' hα'3 hD
    have hcard : Nat.card K = p ^ (2 * f) := by
      rw [hK.card]
      change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    obtain ⟨h3f, -⟩ := eq_frobenius_pow_of_orderOf_eq_three hK.prime (by
      have := hK.one_le; omega) hcard hσ3
    have h3f' : 3 ∣ f := by
      have hc : Nat.Coprime 3 2 := by norm_num
      exact hc.dvd_of_dvd_mul_left h3f
    have hp2 : p = 2 := hp.resolve_right (by
      obtain ⟨f₀, hf₀⟩ := h3f'
      have := hK.one_le
      omega)
    subst hp2
    have : CharP K 2 := hK.charP
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    set w : unitarySU 2 f K 3 := ⟨swapGL, swapGL_mem_unitarySU h h2⟩ with hw
    have hwσ : suField h σ w = w := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_suField, coe_glAut]
      exact swapMat_map σ
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq, Subgroup.coe_one, Units.val_one]
      exact swapMat_mul_self
    have hfix : α' (psuConj h H (unitaryProj h 3 w)) = psuConj h H (unitaryProj h 3 w) := by
      rw [hαH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, psuField_unitaryProj,
        hwσ]
    refine ⟨ψ.symm (psuConj h H (unitaryProj h 3 w)), ?_, ?_, ?_⟩
    · rw [psuConj_unitaryProj, hproj]
      intro h1
      have h2' := congrArg (fun m : projImage (slPi false 3 (2 ^ f) K) =>
        (m : ProjGenLinGroup (Fin 3) K)) h1
      simp only [coe_suToPsu, coe_suConj, Subgroup.coe_one] at h2'
      obtain ⟨c, hc⟩ := mk_eq_one_iff_mem_statedScalars.mp h2'
      rw [Subgroup.coe_inv] at hc
      have h3 : (swapGL : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
        have e1 : ((w : GL (Fin 3) K)) = (H : GL (Fin 3) K)⁻¹ *
            GeneralLinearGroup.scalar (Fin 3) c * H := by
          rw [hc]
          group
        rw [mul_assoc, ← commute_of_mem_statedScalars ⟨c, rfl⟩ (H : GL (Fin 3) K),
          inv_mul_cancel_left] at e1
        exact e1
      have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h3
      have h11 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) h3
      simp [coe_swapGL, swapMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
      rw [← h00] at h11
      exact one_ne_zero h11.symm
    · rw [← map_pow, ← map_pow, ← map_pow, hw2, map_one, map_one, map_one]
    · have h1 : α (ψ.symm (psuConj h H (unitaryProj h 3 w))) =
          ψ.symm (α' (psuConj h H (unitaryProj h 3 w))) := by
        rw [hα', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [h1, hfix]

end Unitary

section Dichotomy

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

theorem aut_pgl_or_fix (hK : PiField π p f K) (hq2 : π = false → 2 < p ^ f)
    (hp : p = 2 ∨ f ≤ 2) (α : MulAut (projImage (slPi π 3 (p ^ f) K))) (hα3 : α ^ 3 = 1) :
    (∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
        (α m : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹) ∨
    ∃ m : projImage (slPi π 3 (p ^ f) K), m ≠ 1 ∧ m ^ p = 1 ∧ α m = m := by
  cases π
  · exact aut_pgl_or_fix_unitary hK (hq2 rfl) hp α hα3
  · exact aut_pgl_or_fix_linear hK hp α hα3

end Dichotomy

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
