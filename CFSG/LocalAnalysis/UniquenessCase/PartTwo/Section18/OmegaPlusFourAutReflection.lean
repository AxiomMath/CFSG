module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOmEq
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.F918Z5ATensor
public import CFSG.Quasithin.Background.SimsG4OrthPlusModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOKronFix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.Quasithin.SimsG4.OrthPlus
open CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance.SL2Char2
open CFSG.EvenSporadicStandard.M24Std
open Matrix
open scoped Matrix MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem o4p_toMat_injective : Function.Injective (OmegaModel.toMat (K := K)) := by
  intro x y h
  have := congrArg (OmegaModel.ofMat) h
  simpa only [OmegaModel.ofMat_toMat] using this

theorem o4p_quadPlus_eq_det (v : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K v = (OmegaModel.toMat v).det := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, OmegaModel.toMat,
    Fin.sum_univ_two, Matrix.det_fin_two_of]
  rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem polQ_eq_polar_det (v w : Fin 2 ⊕ Fin 2 → K) :
    polQ v w = QuadraticMap.polar (determinantForm K) (OmegaModel.toMat v)
      (OmegaModel.toMat w) := by
  simp only [polQ, QuadraticMap.polar, o4p_quadPlus_eq_det, OmegaModel.toMat_add,
    determinantForm_apply]

theorem exists_normalized_reflection
    {e : Fin 2 ⊕ Fin 2 → K} (he : StatedQuadPlus 2 K e ≠ 0) :
    ∃ e' : Fin 2 ⊕ Fin 2 → K, StatedQuadPlus 2 K e' = 1 ∧
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        (polQ v e' / StatedQuadPlus 2 K e') • e' =
          (polQ v e / StatedQuadPlus 2 K e) • e := by
  obtain ⟨c, hc'⟩ := isSquare_of_charTwo' (StatedQuadPlus 2 K e)
  have hc : c ^ 2 = StatedQuadPlus 2 K e := by rw [hc', sq]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    exact he (by simpa using hc.symm)
  refine ⟨c⁻¹ • e, ?_, ?_⟩
  · rw [quadPlus_smul, ← hc]
    field_simp
  · intro v
    have hQ' : StatedQuadPlus 2 K (c⁻¹ • e) = 1 := by
      rw [quadPlus_smul, ← hc]
      field_simp
    rw [hQ', div_one, polQ_smul_right, ← hc, smul_smul, div_eq_mul_inv]
    congr 1
    have hc2 : (c ^ 2)⁻¹ = c⁻¹ * c⁻¹ := by
      field_simp
    rw [hc2]
    ring

theorem exists_toMat_reflection_eq_adj {r : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    {e : Fin 2 ⊕ Fin 2 → K}
    (hr : ∀ v, toAddMap r v = v + (polQ v e / StatedQuadPlus 2 K e) • e)
    (he : StatedQuadPlus 2 K e ≠ 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, S.det = 1 ∧
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        OmegaModel.toMat (toAddMap r v) = S * (OmegaModel.toMat v).adjugate * S := by
  obtain ⟨e', hQe', hform⟩ := exists_normalized_reflection (K := K) he
  have hdiv : ∀ v, polQ v e' • e' =
      (polQ v e' / StatedQuadPlus 2 K e') • e' := by
    intro v
    rw [div_eq_mul_inv, hQe', inv_one, mul_one]
  have hr' : ∀ v, toAddMap r v = v + polQ v e' • e' := by
    intro v
    rw [hr v, hdiv v, hform v]
  refine ⟨OmegaModel.toMat e', ?_, ?_⟩
  · rw [← o4p_quadPlus_eq_det, hQe']
  · intro v
    rw [hr', OmegaModel.toMat_add, OmegaModel.toMat_smul, polQ_eq_polar_det]
    exact refl_det_eq _ _ (by rw [← o4p_quadPlus_eq_det, hQe'])

theorem adjugate_eq_inv_of_det_eq_one' {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det = 1) :
    S.adjugate = S⁻¹ := by
  have h1 : S * S.adjugate = 1 := by
    rw [Matrix.mul_adjugate, hS, one_smul]
  exact (Matrix.inv_eq_right_inv h1).symm

theorem adjugate_coe_sl2 (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((x : Matrix (Fin 2) (Fin 2) K).adjugate) =
      ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  simpa only [Matrix.SpecialLinearGroup.coe_inv] using adjugate_eq_inv_of_det_eq_one' x.2

theorem adjugate_coe_sl2_inv (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).adjugate) =
      ((x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [adjugate_coe_sl2, inv_inv]

theorem o4p_coe_inv_sl2 (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : Matrix (Fin 2) (Fin 2) K))⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_inv_of_det_eq_one' x.2]

theorem coe_mul_inv_sl2 (S x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((S * x * S⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (S : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
        (S : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, o4p_coe_inv_sl2]

theorem coe_inv_mul_sl2 (S x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((S⁻¹ * x * S : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (S : Matrix (Fin 2) (Fin 2) K)⁻¹ * (x : Matrix (Fin 2) (Fin 2) K) *
        (S : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, o4p_coe_inv_sl2]

theorem o4p_reflection_mul_self {r : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det = 1)
    (hR : ∀ v, OmegaModel.toMat (toAddMap r v) =
      S * (OmegaModel.toMat v).adjugate * S) :
    r * r = 1 := by
  have hSadj : S.adjugate = S⁻¹ := adjugate_eq_inv_of_det_eq_one' hS
  have hSunit : IsUnit S.det := by rw [hS]; exact isUnit_one
  have hSS : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSunit
  have hSiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSunit
  apply toAddMap_injective
  intro v
  rw [toAddMap_mul, toAddMap_one]
  apply o4p_toMat_injective
  rw [hR, hR]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hSadj,
    CFSG.Quasithin.SimsG4.OrthPlus.adjugate_adjugate_two]
  calc S * (S⁻¹ * (OmegaModel.toMat v * S⁻¹)) * S
      = (S * S⁻¹) * OmegaModel.toMat v * (S⁻¹ * S) := by noncomm_ring
    _ = OmegaModel.toMat v := by rw [hSS, hSiS]; simp

theorem om4_toMat_eq_omegaToMat (v : Fin 2 ⊕ Fin 2 → K) :
    CFSG.Quasithin.G11.P3Ortho.Om4.toMat K v = OmegaModel.toMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Quasithin.G11.P3Ortho.Om4.toMat, OmegaModel.toMat, CharTwo.neg_eq]

noncomputable def omegaReflEquiv (h4 : 4 ≤ Nat.card K) :
    ↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
      (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
  Classical.choose (s16c13bcA_omega_equiv_apply (K := K) h4)

theorem omegaReflEquiv_action (h4 : 4 ≤ Nat.card K)
    (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (v : Fin 2 ⊕ Fin 2 → K) :
    OmegaModel.toMat (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) *
        OmegaModel.toMat v *
        (((omegaReflEquiv (K := K) h4 γ).2⁻¹ :
          Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [← om4_toMat_eq_omegaToMat, ← om4_toMat_eq_omegaToMat]
  exact Classical.choose_spec (s16c13bcA_omega_equiv_apply (K := K) h4) γ v

theorem toMat_natAut_omegaReflEquiv (h4 : 4 ≤ Nat.card K)
    (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (v : Fin 2 ⊕ Fin 2 → K) :
    OmegaModel.toMat (toAddMap (natAut (StatedOmega (StatedQuadPlus 2 K)) γ) v) =
      ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) *
        OmegaModel.toMat v *
        (((omegaReflEquiv (K := K) h4 γ).2⁻¹ :
          Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  rw [toAddMap_natAut]
  exact omegaReflEquiv_action h4 γ v

theorem omegaReflEquiv_reflection (h4 : 4 ≤ Nat.card K)
    {r : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} {S : Matrix (Fin 2) (Fin 2) K}
    (hS : S.det = 1)
    (hR : ∀ v, OmegaModel.toMat (toAddMap r v) =
      S * (OmegaModel.toMat v).adjugate * S)
    (hr : r * r = 1) (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) :
    ∃ δ : ↥(StatedOmega (StatedQuadPlus 2 K)),
      ∃ b' a' : Matrix.SpecialLinearGroup (Fin 2) K,
        omegaReflEquiv (K := K) h4 δ = (b', a') ∧
        (b' : Matrix (Fin 2) (Fin 2) K) =
          S * ((omegaReflEquiv (K := K) h4 γ).2 : Matrix (Fin 2) (Fin 2) K) * S⁻¹ ∧
        (a' : Matrix (Fin 2) (Fin 2) K) =
          S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) * S ∧
        natAut (StatedOmega (StatedQuadPlus 2 K)) δ =
          r * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r⁻¹ := by
  have hSinv : S⁻¹.det = 1 := by
    rw [Matrix.det_nonsing_inv, hS]
    simp
  let b' : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨S * ((omegaReflEquiv (K := K) h4 γ).2 : Matrix (Fin 2) (Fin 2) K) * S⁻¹, by
      rw [Matrix.det_mul, Matrix.det_mul, hS, (omegaReflEquiv (K := K) h4 γ).2.2, hSinv]
      simp⟩
  let a' : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) * S, by
      rw [Matrix.det_mul, Matrix.det_mul, hSinv, (omegaReflEquiv (K := K) h4 γ).1.2, hS]
      simp⟩
  let δ : ↥(StatedOmega (StatedQuadPlus 2 K)) :=
    (omegaReflEquiv (K := K) h4).symm (b', a')
  have hδ : omegaReflEquiv (K := K) h4 δ = (b', a') := by
    simp [δ]
  have hb' : (b' : Matrix (Fin 2) (Fin 2) K) =
      S * ((omegaReflEquiv (K := K) h4 γ).2 : Matrix (Fin 2) (Fin 2) K) * S⁻¹ := rfl
  have ha' : (a' : Matrix (Fin 2) (Fin 2) K) =
      S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) * S := rfl
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  have hSadj : S.adjugate = S⁻¹ := adjugate_eq_inv_of_det_eq_one' hS
  have hSunit : IsUnit S.det := by rw [hS]; exact isUnit_one
  have hmain : ∀ (b a : Matrix.SpecialLinearGroup (Fin 2) K)
      (X : Matrix (Fin 2) (Fin 2) K),
      S * (b * (S * X.adjugate * S) * a⁻¹).adjugate * S =
        (S * a * S⁻¹) * X * (S⁻¹ * b⁻¹ * S) := by
    intro b a X
    simp only [Matrix.adjugate_mul_distrib, hSadj,
      CFSG.Quasithin.SimsG4.OrthPlus.adjugate_adjugate_two]
    rw [adjugate_eq_inv_of_det_eq_one' b.2, adjugate_coe_sl2_inv a, o4p_coe_inv_sl2 b]
    simp only [Matrix.mul_assoc]
  have hainv : (((a'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) =
      S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K)⁻¹ * S := by
    rw [o4p_coe_inv_sl2]
    change (S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K) * S)⁻¹ =
      S⁻¹ * ((omegaReflEquiv (K := K) h4 γ).1 : Matrix (Fin 2) (Fin 2) K)⁻¹ * S
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv S hSunit]
    simp only [Matrix.mul_assoc]
  have hmatrix : ∀ v,
      OmegaModel.toMat (toAddMap (r * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r⁻¹) v) =
        (b' : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat v *
          (((a'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro v
    rw [hrinv]
    rw [toAddMap_mul, toAddMap_mul, hR]
    rw [toMat_natAut_omegaReflEquiv h4 γ (toAddMap r v), hR v]
    rw [hmain, hb', hainv, o4p_coe_inv_sl2 (omegaReflEquiv (K := K) h4 γ).1]
  have haction : ∀ v, toAddMap (natAut (StatedOmega (StatedQuadPlus 2 K)) δ) v =
      toAddMap (r * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r⁻¹) v := by
    intro v
    apply o4p_toMat_injective
    rw [toMat_natAut_omegaReflEquiv h4 δ v, hδ]
    exact (hmatrix v).symm
  refine ⟨δ, b', a', hδ, hb', ha', ?_⟩
  exact toAddMap_injective (g := natAut (StatedOmega (StatedQuadPlus 2 K)) δ)
    (h := r * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r⁻¹) haction

noncomputable def o4p_semilinearAut (h4 : 4 ≤ Nat.card K)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K) :
    MulAut (StdMod (Fin 2 ⊕ Fin 2) K) :=
  MulAut.congr (stdOmegaModel h4).matEquiv.symm
    (OmegaModel.matAut g₁ (Matrix.SpecialLinearGroup.transpose g₂⁻¹) *
      matMapEquiv 2 σ)

theorem toMat_semilinearAut (h4 : 4 ≤ Nat.card K)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    OmegaModel.toMat (toAddMap (o4p_semilinearAut (K := K) h4 g₁ g₂ σ) v) =
      (g₁ : Matrix (Fin 2) (Fin 2) K) *
        (OmegaModel.toMat v).map σ * (g₂ : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  let E := (stdOmegaModel h4).matEquiv
  let B : MulAut (Multiplicative (Matrix (Fin 2) (Fin 2) K)) :=
    OmegaModel.matAut g₁ (Matrix.SpecialLinearGroup.transpose g₂⁻¹) * matMapEquiv 2 σ
  have htrans : (((Matrix.SpecialLinearGroup.transpose g₂⁻¹ :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ =
      ((g₂ : Matrix (Fin 2) (Fin 2) K))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose, o4p_coe_inv_sl2]
  have hB : ∀ X : Matrix (Fin 2) (Fin 2) K,
      Multiplicative.toAdd (B (Multiplicative.ofAdd X)) =
        (g₁ : Matrix (Fin 2) (Fin 2) K) * X.map σ *
          (g₂ : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
    intro X
    change (g₁ : Matrix (Fin 2) (Fin 2) K) * (X.map σ) *
        (((Matrix.SpecialLinearGroup.transpose g₂⁻¹ :
          Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ = _
    rw [htrans]
  have hE : E (o4p_semilinearAut (K := K) h4 g₁ g₂ σ
      (Multiplicative.ofAdd v)) = B (E (Multiplicative.ofAdd v)) := by
    rw [o4p_semilinearAut]
    change E (E.symm (B (E (Multiplicative.ofAdd v)))) = B (E (Multiplicative.ofAdd v))
    simp
  calc OmegaModel.toMat (toAddMap (o4p_semilinearAut (K := K) h4 g₁ g₂ σ) v)
      = Multiplicative.toAdd (E (o4p_semilinearAut (K := K) h4 g₁ g₂ σ
          (Multiplicative.ofAdd v))) := rfl
    _ = Multiplicative.toAdd (B (E (Multiplicative.ofAdd v))) := by rw [hE]
    _ = Multiplicative.toAdd (B (Multiplicative.ofAdd (OmegaModel.toMat v))) := rfl
    _ = (g₁ : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).map σ *
          (g₂ : Matrix (Fin 2) (Fin 2) K)⁻¹ := hB _

theorem toMat_semilinearAut_sigma_inv (h4 : 4 ≤ Nat.card K)
    (g₁ g₂ : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (v : Fin 2 ⊕ Fin 2 → K) :
    (OmegaModel.toMat
        (toAddMap (o4p_semilinearAut (K := K) h4 g₁ g₂ σ)⁻¹ v)).map σ =
      (g₁ : Matrix (Fin 2) (Fin 2) K)⁻¹ * OmegaModel.toMat v *
        (g₂ : Matrix (Fin 2) (Fin 2) K) := by
  let A := o4p_semilinearAut (K := K) h4 g₁ g₂ σ
  have h := toMat_semilinearAut h4 g₁ g₂ σ (toAddMap A⁻¹ v)
  rw [toAddMap_inv_apply] at h
  have hg₁ : ((g₁ : Matrix (Fin 2) (Fin 2) K))⁻¹ * (g₁ : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← o4p_coe_inv_sl2, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have hg₂ : ((g₂ : Matrix (Fin 2) (Fin 2) K))⁻¹ * (g₂ : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← o4p_coe_inv_sl2, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  rw [h]
  symm
  calc (g₁ : Matrix (Fin 2) (Fin 2) K)⁻¹ *
        ((g₁ : Matrix (Fin 2) (Fin 2) K) *
          (OmegaModel.toMat (toAddMap A⁻¹ v)).map σ *
            (g₂ : Matrix (Fin 2) (Fin 2) K)⁻¹) *
        (g₂ : Matrix (Fin 2) (Fin 2) K)
      = ((g₁ : Matrix (Fin 2) (Fin 2) K)⁻¹ * (g₁ : Matrix (Fin 2) (Fin 2) K)) *
          (OmegaModel.toMat (toAddMap A⁻¹ v)).map σ *
            ((g₂ : Matrix (Fin 2) (Fin 2) K)⁻¹ * (g₂ : Matrix (Fin 2) (Fin 2) K)) := by
        noncomm_ring
    _ = (OmegaModel.toMat (toAddMap A⁻¹ v)).map σ := by rw [hg₁, hg₂]; simp

theorem o4p_coe_slFieldAut (σ : K ≃+* K) (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((slFieldAut σ x : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K).map σ := rfl

theorem coe_conj_slFieldAut (p : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((MulAut.conj p * slFieldAut σ) x : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      (p : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K).map σ *
        (p : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, o4p_coe_inv_sl2, o4p_coe_slFieldAut]

theorem map_coe_inv_sl2 (σ : K ≃+* K) (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map σ) =
      (((x : Matrix (Fin 2) (Fin 2) K)).map σ)⁻¹ := by
  have hxdet : ((x : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (x : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) K) 0 1 * (x : Matrix (Fin 2) (Fin 2) K) 1 0) = 1 := by
    have h := x.2
    rwa [Matrix.det_fin_two] at h
  have hdet : ((x : Matrix (Fin 2) (Fin 2) K).map σ).det = 1 := by
    simp only [Matrix.det_fin_two, Matrix.map_apply]
    rw [← map_mul, ← map_mul, ← map_sub, hxdet, map_one]
  rw [o4p_coe_inv_sl2 x, ← adjugate_eq_inv_of_det_eq_one' x.2,
    ← adjugate_eq_inv_of_det_eq_one' hdet]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.map_apply]

theorem coe_inv_conj_slFieldAut (q : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((((MulAut.conj q * slFieldAut σ) a)⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (q : Matrix (Fin 2) (Fin 2) K) *
        ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ *
        (q : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  have hqunit : IsUnit ((q : Matrix (Fin 2) (Fin 2) K).det) := by
    rw [q.2]
    exact isUnit_one
  rw [o4p_coe_inv_sl2, coe_conj_slFieldAut q σ a]
  change (((q : Matrix (Fin 2) (Fin 2) K) *
      (a : Matrix (Fin 2) (Fin 2) K).map σ *
      (q : Matrix (Fin 2) (Fin 2) K)⁻¹)⁻¹) =
    (q : Matrix (Fin 2) (Fin 2) K) *
      ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ *
      (q : Matrix (Fin 2) (Fin 2) K)⁻¹
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hqunit,
    map_coe_inv_sl2 σ a]
  simp only [Matrix.mul_assoc]

theorem semilinearAut_conj_coords (h4 : 4 ≤ Nat.card K)
    (p q : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) :
    ∃ δ : ↥(StatedOmega (StatedQuadPlus 2 K)),
      omegaReflEquiv (K := K) h4 δ =
        ((MulAut.conj p * slFieldAut σ) (omegaReflEquiv (K := K) h4 γ).1,
          (MulAut.conj q * slFieldAut σ) (omegaReflEquiv (K := K) h4 γ).2) ∧
      natAut (StatedOmega (StatedQuadPlus 2 K)) δ =
        o4p_semilinearAut (K := K) h4 p q σ *
          natAut (StatedOmega (StatedQuadPlus 2 K)) γ *
          (o4p_semilinearAut (K := K) h4 p q σ)⁻¹ := by
  let A := o4p_semilinearAut (K := K) h4 p q σ
  let b := (omegaReflEquiv (K := K) h4 γ).1
  let a := (omegaReflEquiv (K := K) h4 γ).2
  let b' : Matrix.SpecialLinearGroup (Fin 2) K := (MulAut.conj p * slFieldAut σ) b
  let a' : Matrix.SpecialLinearGroup (Fin 2) K := (MulAut.conj q * slFieldAut σ) a
  let δ : ↥(StatedOmega (StatedQuadPlus 2 K)) := (omegaReflEquiv (K := K) h4).symm (b', a')
  have hδ : omegaReflEquiv (K := K) h4 δ = (b', a') := by
    simp [δ]
  have hb' : (b' : Matrix (Fin 2) (Fin 2) K) =
      (p : Matrix (Fin 2) (Fin 2) K) * (b : Matrix (Fin 2) (Fin 2) K).map σ *
        (p : Matrix (Fin 2) (Fin 2) K)⁻¹ :=
    coe_conj_slFieldAut p σ b
  have ha' : ((a'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) =
      (q : Matrix (Fin 2) (Fin 2) K) *
        ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ *
        (q : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
    change ((((MulAut.conj q * slFieldAut σ) a)⁻¹ :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    exact coe_inv_conj_slFieldAut q σ a
  have hmain : ∀ v,
      OmegaModel.toMat (toAddMap (A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹) v) =
        (b' : Matrix (Fin 2) (Fin 2) K) * OmegaModel.toMat v *
          (((a'⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    intro v
    rw [toAddMap_mul, toAddMap_mul,
      toMat_semilinearAut h4 p q σ,
      toMat_natAut_omegaReflEquiv h4 γ (toAddMap A⁻¹ v)]
    rw [Matrix.map_mul, Matrix.map_mul,
      toMat_semilinearAut_sigma_inv h4 p q σ v, hb', ha', map_coe_inv_sl2 σ a]
    simp only [Matrix.mul_assoc, b, a]
  have haction : ∀ v, toAddMap (natAut (StatedOmega (StatedQuadPlus 2 K)) δ) v =
      toAddMap (A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹) v := by
    intro v
    apply o4p_toMat_injective
    rw [toMat_natAut_omegaReflEquiv h4 δ v, hδ]
    exact (hmain v).symm
  refine ⟨δ, hδ, ?_⟩
  exact toAddMap_injective (g := natAut (StatedOmega (StatedQuadPlus 2 K)) δ)
    (h := A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹) haction

theorem exists_sl2_trace_eq (t : K) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) K, (x : Matrix (Fin 2) (Fin 2) K).trace = t := by
  refine ⟨⟨!![(0 : K), 1; 1, t], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two]
    simp [CharTwo.neg_eq]
  · rw [Matrix.trace_fin_two]
    simp

theorem trace_conj_det_one {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det = 1)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (S * M * S⁻¹).trace = M.trace := by
  have hSunit : IsUnit S.det := by rw [hS]; exact isUnit_one
  calc (S * M * S⁻¹).trace = (S⁻¹ * (S * M)).trace := Matrix.trace_mul_comm (S * M) S⁻¹
    _ = ((S⁻¹ * S) * M).trace := by rw [Matrix.mul_assoc]
    _ = M.trace := by rw [Matrix.nonsing_inv_mul S hSunit, Matrix.one_mul]

theorem trace_conj_inv_det_one {S : Matrix (Fin 2) (Fin 2) K} (hS : S.det = 1)
    (M : Matrix (Fin 2) (Fin 2) K) :
    (S⁻¹ * M * S).trace = M.trace := by
  have hSunit : IsUnit S.det := by rw [hS]; exact isUnit_one
  calc (S⁻¹ * M * S).trace = (S * (S⁻¹ * M)).trace := Matrix.trace_mul_comm (S⁻¹ * M) S
    _ = ((S * S⁻¹) * M).trace := by rw [Matrix.mul_assoc]
    _ = M.trace := by rw [Matrix.mul_nonsing_inv S hSunit, Matrix.one_mul]

theorem trace_coe_conj_slFieldAut (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : K ≃+* K)
    (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((((MulAut.conj g * slFieldAut σ) x : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)).trace = σ ((x : Matrix (Fin 2) (Fin 2) K).trace) := by
  rw [coe_conj_slFieldAut, trace_conj_det_one g.2]
  exact CFSG.ComponentClassification.Burgoyne.O.trace_map_ringEquiv σ (x : Matrix (Fin 2) (Fin 2) K)

def reflCoords (S : Matrix.SpecialLinearGroup (Fin 2) K)
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K :=
  (S * x.2 * S⁻¹, S⁻¹ * x.1 * S)

theorem omegaReflEquiv_reflection_sl (h4 : 4 ≤ Nat.card K)
    {r : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    {S : Matrix.SpecialLinearGroup (Fin 2) K}
    (hR : ∀ v, OmegaModel.toMat (toAddMap r v) =
      (S : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).adjugate *
        (S : Matrix (Fin 2) (Fin 2) K))
    (hr : r * r = 1) (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) :
    ∃ δ : ↥(StatedOmega (StatedQuadPlus 2 K)),
      omegaReflEquiv (K := K) h4 δ = reflCoords S (omegaReflEquiv (K := K) h4 γ) ∧
      natAut (StatedOmega (StatedQuadPlus 2 K)) δ =
        r * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r⁻¹ := by
  obtain ⟨δ, b', a', hδ, hb', ha', hnat⟩ :=
    omegaReflEquiv_reflection h4 S.2 hR hr γ
  have hpair : (b', a') = reflCoords S (omegaReflEquiv (K := K) h4 γ) := by
    apply Prod.ext
    · apply Subtype.ext
      simpa [reflCoords, o4p_coe_inv_sl2 S] using hb'
    · apply Subtype.ext
      simpa [reflCoords, o4p_coe_inv_sl2 S] using ha'
  exact ⟨δ, hδ.trans hpair, hnat⟩

theorem reflCoords_relation (h4 : 4 ≤ Nat.card K)
    {r₀ r₁ : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    {S₀ S₁ : Matrix.SpecialLinearGroup (Fin 2) K}
    (hR₀ : ∀ v, OmegaModel.toMat (toAddMap r₀ v) =
      (S₀ : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).adjugate *
        (S₀ : Matrix (Fin 2) (Fin 2) K))
    (hR₁ : ∀ v, OmegaModel.toMat (toAddMap r₁ v) =
      (S₁ : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).adjugate *
        (S₁ : Matrix (Fin 2) (Fin 2) K))
    (hr₀ : r₀ * r₀ = 1) (hr₁ : r₁ * r₁ = 1)
    (θ : MulAut ↥(StatedOmega (StatedQuadPlus 2 K)))
    (hθ : ∀ γ γ' : ↥(StatedOmega (StatedQuadPlus 2 K)),
      r₁ * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r₁⁻¹ =
        natAut (StatedOmega (StatedQuadPlus 2 K)) γ' →
      natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ') =
        r₀ * natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ) * r₀⁻¹)
    (x : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    (MulAut.congr (omegaReflEquiv (K := K) h4) θ) (reflCoords S₁ x) =
      reflCoords S₀ ((MulAut.congr (omegaReflEquiv (K := K) h4) θ) x) := by
  let ε := omegaReflEquiv (K := K) h4
  let α := MulAut.congr ε θ
  let γ : ↥(StatedOmega (StatedQuadPlus 2 K)) := ε.symm x
  have hγ : ε γ = x := by simp [γ]
  obtain ⟨δ₁, hδ₁, hnat₁⟩ := omegaReflEquiv_reflection_sl h4 hR₁ hr₁ γ
  have hpre : r₁ * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r₁⁻¹ =
      natAut (StatedOmega (StatedQuadPlus 2 K)) δ₁ := hnat₁.symm
  have hθδ := hθ γ δ₁ hpre
  obtain ⟨δ₀, hδ₀, hnat₀⟩ := omegaReflEquiv_reflection_sl h4 hR₀ hr₀ (θ γ)
  have hδeq : δ₀ = θ δ₁ := by
    apply natAut_injective (StatedOmega (StatedQuadPlus 2 K))
    rw [hnat₀, hθδ]
  calc α (reflCoords S₁ x)
      = α (ε δ₁) := by rw [← hγ, ← hδ₁]
    _ = ε (θ δ₁) := by
      simp [α, MulAut.congr_apply]
    _ = ε δ₀ := by rw [← hδeq]
    _ = reflCoords S₀ (ε (θ γ)) := hδ₀
    _ = reflCoords S₀ (α (ε γ)) := by
      rw [show α (ε γ) = ε (θ γ) by
        simp [α, MulAut.congr_apply]]
    _ = reflCoords S₀ (α x) := by rw [hγ]

theorem mem_natNorm_of_conj {A : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    {θ : MulAut ↥(StatedOmega (StatedQuadPlus 2 K))}
    (h : ∀ γ : ↥(StatedOmega (StatedQuadPlus 2 K)),
      A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹ =
        natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ)) :
    A ∈ natNorm (StatedOmega (StatedQuadPlus 2 K)) := by
  rw [natNorm, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨θ γ, (h γ).symm⟩
  · rintro ⟨γ, hγ⟩
    have h1 := h (θ.symm γ)
    have hEq : A * x * A⁻¹ =
        A * natAut (StatedOmega (StatedQuadPlus 2 K)) (θ.symm γ) * A⁻¹ := by
      rw [← hγ, h1]
      simp
    have : x = natAut (StatedOmega (StatedQuadPlus 2 K)) (θ.symm γ) := by
      simpa [mul_assoc] using congrArg (fun z => A⁻¹ * z * A) hEq
    exact ⟨θ.symm γ, this.symm⟩

theorem conj_slFieldAut_mul_inv_left (g S x : Matrix.SpecialLinearGroup (Fin 2) K)
    (σ : K ≃+* K) :
    (MulAut.conj (g * (slFieldAut σ S)⁻¹) * slFieldAut σ) (S * x * S⁻¹) =
      (MulAut.conj g * slFieldAut σ) x := by
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group
  rw [MulAut.mul_apply, MulAut.conj_apply, _root_.zpow_neg_one]

theorem conj_slFieldAut_mul_right (g S x : Matrix.SpecialLinearGroup (Fin 2) K)
    (σ : K ≃+* K) :
    (MulAut.conj (g * slFieldAut σ S) * slFieldAut σ) (S⁻¹ * x * S) =
      (MulAut.conj g * slFieldAut σ) x := by
  rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  group
  rw [MulAut.mul_apply, MulAut.conj_apply, _root_.zpow_neg_one]

theorem exists_semilinear_of_conj_reflections (hK : Nat.card K = 4)
    (θ : MulAut ↥(StatedOmega (StatedQuadPlus 2 K)))
    {e₀ e₁ : Fin 2 ⊕ Fin 2 → K}
    {r₀ r₁ : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)}
    (hr₀ : ∀ v, toAddMap r₀ v = v + (polQ v e₀ / StatedQuadPlus 2 K e₀) • e₀)
    (hr₁ : ∀ v, toAddMap r₁ v = v + (polQ v e₁ / StatedQuadPlus 2 K e₁) • e₁)
    (he₀ : StatedQuadPlus 2 K e₀ ≠ 0) (he₁ : StatedQuadPlus 2 K e₁ ≠ 0)
    (hθ : ∀ γ γ' : ↥(StatedOmega (StatedQuadPlus 2 K)),
      r₁ * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r₁⁻¹ =
        natAut (StatedOmega (StatedQuadPlus 2 K)) γ' →
      natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ') =
        r₀ * natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ) * r₀⁻¹) :
    ∃ A ∈ natNorm (StatedOmega (StatedQuadPlus 2 K)),
      ∀ γ, natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ) =
        A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹ := by
  classical
  have h4 : 4 ≤ Nat.card K := by omega
  obtain ⟨S₀, hS₀, hR₀⟩ := exists_toMat_reflection_eq_adj (K := K) hr₀ he₀
  obtain ⟨S₁, hS₁, hR₁⟩ := exists_toMat_reflection_eq_adj (K := K) hr₁ he₁
  let S₀' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨S₀, hS₀⟩
  let S₁' : Matrix.SpecialLinearGroup (Fin 2) K := ⟨S₁, hS₁⟩
  have hR₀' : ∀ v, OmegaModel.toMat (toAddMap r₀ v) =
      (S₀' : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).adjugate *
        (S₀' : Matrix (Fin 2) (Fin 2) K) := hR₀
  have hR₁' : ∀ v, OmegaModel.toMat (toAddMap r₁ v) =
      (S₁' : Matrix (Fin 2) (Fin 2) K) * (OmegaModel.toMat v).adjugate *
        (S₁' : Matrix (Fin 2) (Fin 2) K) := hR₁
  have hr₀mul : r₀ * r₀ = 1 := o4p_reflection_mul_self hS₀ hR₀
  have hr₁mul : r₁ * r₁ = 1 := o4p_reflection_mul_self hS₁ hR₁
  let ε := omegaReflEquiv (K := K) h4
  let α := MulAut.congr ε θ
  have hα_app : ∀ γ : ↥(StatedOmega (StatedQuadPlus 2 K)), α (ε γ) = ε (θ γ) := by
    intro γ
    simp [α, MulAut.congr_apply]
  have hrel := reflCoords_relation (K := K) h4 hR₀' hR₁' hr₀mul hr₁mul θ hθ
  have hsimpleGroup : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.Quasithin.H13.U4Par.isSimpleGroup_sl2_of_charTwo (F := K) h4
  have hsimple : ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      N.Normal → N = ⊥ ∨ N = ⊤ :=
    fun N _ => hsimpleGroup.eq_bot_or_eq_top_of_normal N
  have hcentral : ∀ a : Matrix.SpecialLinearGroup (Fin 2) K,
      (∀ c, a * c = c * a) → a = 1 := by
    intro a ha
    have hmem : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Subgroup.mem_center_iff.mpr (fun g => (ha g).symm)
    have hbot : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
      CFSG.Quasithin.H13.U4Par.center_sl2_eq_bot_of_charTwo (F := K)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hnt : ∃ s : Matrix.SpecialLinearGroup (Fin 2) K, s ≠ 1 := by
    refine ⟨tU (K := K) 1, fun h => ?_⟩
    have h0 : tU (K := K) 1 = tU (K := K) 0 := by simpa [tU_zero] using h
    exact one_ne_zero (tU_injective (K := K) h0)
  rcases ProdAut.mulAut_prod_cases hsimple hcentral hnt α with hp | hs
  ·
    obtain ⟨α₁, α₂, hαapply⟩ := ProdAut.exists_prod_preserve α hp.1 hp.2
    obtain ⟨g₁, σ₁, hα₁⟩ := exists_conj_fieldAut α₁
    obtain ⟨g₂, σ₂, hα₂⟩ := exists_conj_fieldAut α₂
    have hA : ∀ a : Matrix.SpecialLinearGroup (Fin 2) K,
        α₁ (S₁' * a * S₁'⁻¹) = S₀' * α₂ a * S₀'⁻¹ := by
      intro a
      have h := congrArg Prod.fst (hrel (1, a))
      have h1 : reflCoords S₁' (1, a) = (S₁' * a * S₁'⁻¹, 1) := by simp [reflCoords]
      have hmid : α (S₁' * a * S₁'⁻¹, 1) =
          (α₁ (S₁' * a * S₁'⁻¹), α₂ 1) := hαapply _ _
      have h2 : α (1, a) = (α₁ 1, α₂ a) := hαapply _ _
      rw [h1, hmid, h2] at h
      simpa [reflCoords] using h
    have hσ : σ₁ = σ₂ := by
      ext t
      obtain ⟨a, ha⟩ := exists_sl2_trace_eq (K := K) t
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
        ((x : Matrix (Fin 2) (Fin 2) K).trace)) (hA a)
      rw [hα₁, trace_coe_conj_slFieldAut, coe_mul_inv_sl2 S₁' a,
        trace_conj_det_one S₁'.2, ha,
        hα₂, coe_mul_inv_sl2 S₀' ((MulAut.conj g₂ * slFieldAut σ₂) a),
        trace_conj_det_one S₀'.2, trace_coe_conj_slFieldAut, ha] at h
      exact h
    have hα₁' : α₁ = MulAut.conj g₁ * slFieldAut σ₂ := by
      rw [hα₁, hσ]
    let A := o4p_semilinearAut (K := K) h4 g₁ g₂ σ₂
    have hconj : ∀ γ : ↥(StatedOmega (StatedQuadPlus 2 K)),
        natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ) =
          A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹ := by
      intro γ
      obtain ⟨δ, hδ, hnat⟩ := semilinearAut_conj_coords (K := K) h4 g₁ g₂ σ₂ γ
      have hεθ : ε (θ γ) = ε δ := by
        rw [← hα_app γ, hαapply, hα₁', hα₂]
        exact hδ.symm
      have hδθ : θ γ = δ := ε.injective hεθ
      rw [hδθ]
      exact hnat
    exact ⟨A, mem_natNorm_of_conj (fun γ => (hconj γ).symm), hconj⟩
  ·
    obtain ⟨α₁, α₂, hαapply⟩ := ProdAut.exists_prod_swap α hs.1 hs.2
    obtain ⟨g₁, σ₁, hα₁⟩ := exists_conj_fieldAut α₁
    obtain ⟨g₂, σ₂, hα₂⟩ := exists_conj_fieldAut α₂
    have hA : ∀ b : Matrix.SpecialLinearGroup (Fin 2) K,
        α₁ (S₁'⁻¹ * b * S₁') = S₀' * α₂ b * S₀'⁻¹ := by
      intro b
      have h := congrArg Prod.fst (hrel (b, 1))
      have h1 : reflCoords S₁' (b, 1) = (1, S₁'⁻¹ * b * S₁') := by simp [reflCoords]
      have hmid : α (1, S₁'⁻¹ * b * S₁') =
          (α₁ (S₁'⁻¹ * b * S₁'), α₂ 1) := hαapply _ _
      have h2 : α (b, 1) = (α₁ 1, α₂ b) := hαapply _ _
      rw [h1, hmid, h2] at h
      simpa [reflCoords] using h
    have hσ : σ₁ = σ₂ := by
      ext t
      obtain ⟨b, hb⟩ := exists_sl2_trace_eq (K := K) t
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
        ((x : Matrix (Fin 2) (Fin 2) K).trace)) (hA b)
      rw [hα₁, trace_coe_conj_slFieldAut, coe_inv_mul_sl2 S₁' b,
        trace_conj_inv_det_one S₁'.2 (b : Matrix (Fin 2) (Fin 2) K), hb,
        hα₂, coe_mul_inv_sl2 S₀' ((MulAut.conj g₂ * slFieldAut σ₂) b),
        trace_conj_det_one S₀'.2, trace_coe_conj_slFieldAut, hb] at h
      exact h
    have hα₁' : α₁ = MulAut.conj g₁ * slFieldAut σ₂ := by
      rw [hα₁, hσ]
    have hα₂' : α₂ = MulAut.conj g₂ * slFieldAut σ₂ := hα₂
    let T := slFieldAut σ₂ S₁'
    let p := g₁ * T⁻¹
    let q := g₂ * T
    let B := o4p_semilinearAut (K := K) h4 p q σ₂
    let A := B * r₁
    have hconj : ∀ γ : ↥(StatedOmega (StatedQuadPlus 2 K)),
        natAut (StatedOmega (StatedQuadPlus 2 K)) (θ γ) =
          A * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * A⁻¹ := by
      intro γ
      obtain ⟨δ₁, hδ₁, hnat₁⟩ := omegaReflEquiv_reflection_sl (K := K) h4 hR₁' hr₁mul γ
      obtain ⟨δ₂, hδ₂, hnat₂⟩ := semilinearAut_conj_coords (K := K) h4 p q σ₂ δ₁
      have hεθ : ε (θ γ) = ε δ₂ := by
        rw [← hα_app γ, hαapply, hα₁', hα₂']
        rw [hδ₁] at hδ₂
        simp only [reflCoords] at hδ₂
        rw [show p = g₁ * (slFieldAut σ₂ S₁')⁻¹ from rfl,
          show q = g₂ * slFieldAut σ₂ S₁' from rfl] at hδ₂
        rw [conj_slFieldAut_mul_inv_left g₁ S₁' (ε γ).2 σ₂,
          conj_slFieldAut_mul_right g₂ S₁' (ε γ).1 σ₂] at hδ₂
        exact hδ₂.symm
      have hδ₂θ : θ γ = δ₂ := ε.injective hεθ
      rw [hδ₂θ]
      rw [hnat₂, hnat₁]
      show B * (r₁ * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * r₁⁻¹) * B⁻¹ =
        (B * r₁) * natAut (StatedOmega (StatedQuadPlus 2 K)) γ * (B * r₁)⁻¹
      group
    exact ⟨A, mem_natNorm_of_conj (fun γ => (hconj γ).symm), hconj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
