module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityOuter

public section

namespace CFSG.StandardType

namespace Triality

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {K : Type} [Field K]

section Proj

variable [Finite K] [CharP K 2]

theorem exists_form_ne_zero : ∃ v, coordinateQuadPlus 4 K v ≠ 0 :=
  ⟨_, AutOm.plusUnitVector_form_ne_zero one_le_four⟩

noncomputable abbrev projEquiv8 : Om8 K ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K) :=
  derivedProjEquiv _ exists_form_ne_zero

theorem exists_pair_of_mem_image {α : MulAut (Om8 K)}
    (hα : MulAut.congr projEquiv8 α ∈ matrixProjectiveImage (coordinateQuadPlus 4 K)) :
    ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = α := by
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).1 hα
  refine ⟨g, MulEquiv.ext fun A => ?_⟩
  have h1 : projEquiv8 (α A) = projEquiv8 (matrixDerivedConjugation _ g A) := by
    have h2 : MulAut.congr projEquiv8 α (projEquiv8 A) = projEquiv8 (α A) :=
      congr_apply_apply' projEquiv8 α A
    rw [← h2, ← hg]
    exact matrixProjectiveConjugation_mk _ g A
  exact (projEquiv8.injective h1).symm

theorem congr_conjAct_mem_image (g : similarityPairs (coordinateQuadPlus 4 K)) :
    MulAut.congr projEquiv8 (conjAct _ g) ∈ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  refine (mem_matrixProjectiveImage_iff _ _).2 ⟨g, MulEquiv.ext fun x => ?_⟩
  obtain ⟨A, rfl⟩ := projEquiv8.surjective x
  rw [congr_apply_apply']
  exact matrixProjectiveConjugation_mk _ g A

end Proj

section Family

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (coordinate_plus_pointFamily_orbit_subset plusCX plusCXstar)

variable [Finite K]

theorem pointFamilyAut_eq_image :
    projectivePointFamilyAut (coordinateQuadPlus 4 K) =
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  obtain ⟨f, hf, hK⟩ := CFSG.RankThree.PartOne.KCOrthogonalAut.exists_card_eq_pow K
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K))) .POmegaPlus 4
      (ringChar K) f := ⟨⟨hp, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  exact coordinate_plus_family_eq_matrixImage hmod K hK (MulEquiv.refl _)

theorem smul_pointFamily_cases (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
    a • projectivePointFamily (coordinateQuadPlus 4 K) =
        projectivePointFamily (coordinateQuadPlus 4 K) ∨
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
        plusCX 4 K ∨
      a • projectivePointFamily (coordinateQuadPlus 4 K) =
        plusCXstar 4 K (by norm_num) := by
  have h := coordinate_plus_pointFamily_orbit_subset (n := 4) (K := K) rfl
    (MulAction.mem_orbit _ a)
  simpa using h

end Family

section Pair

open CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldPair fieldPair_val)

variable [Finite K] [CharP K 2]

theorem exists_inner_mul_plusCompl_of_pair (g : similarityPairs (coordinateQuadPlus 4 K)) :
    ∃ ι ∈ inner (Om8 K), ∃ c ∈ AutOm.plusCompl (K := K) one_le_four, conjAct _ g = ι * c := by
  have hn : 1 ≤ 4 := one_le_four
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hv0 := AutOm.plusUnitVector_form_ne_zero (K := K) hn
  set σ := g.val.right with hσ
  have hℓ : (g * (fieldPair (coordinateQuadPlus 4 K) σ
      (E7Pilot.coordinateQuadPlus_fieldMap 4 σ))⁻¹).val.right = 1 := by
    rw [← fieldProjection_apply, map_mul, map_inv, fieldProjection_apply, fieldProjection_apply,
      fieldPair_val, SemidirectProduct.right_inr, ← hσ, mul_inv_cancel]
  obtain ⟨B, hB⟩ := CFSG.RankThree.PartOne.OutStructure.exists_isometry_of_linear _ ⟨_, hv0⟩
    ⟨_, (mem_linearSimilarityPairs_iff _ _).2 hℓ⟩
  have hℓB := conjAct_eq_of_isometry hB
  have hα : conjAct (coordinateQuadPlus 4 K) g =
      conjAct (coordinateQuadPlus 4 K) (matrixIsometryInclusion _ B) * AutOm.fieldAutP 4 σ := by
    rw [← hℓB, AutOm.fieldAutP_apply, ← map_mul, inv_mul_cancel_right]
  rcases mem_or_mul_reflMat_mem hnd hT B.2 (OmegaPilot.plusUnitVector hn) hv0 with hBΓ | hBΓ
  · exact ⟨_, conjAct_inclusion_mem_inner B hBΓ, _, ⟨σ, Or.inl rfl⟩, hα⟩
  · have hR := reflMat_mem_isometries (Q := coordinateQuadPlus 4 K)
      (OmegaPilot.plusUnitVector hn) hv0
    have hιB : matrixIsometryInclusion (coordinateQuadPlus 4 K) B =
        matrixIsometryInclusion (coordinateQuadPlus 4 K)
          ⟨B.val * reflMat _ (OmegaPilot.plusUnitVector hn) hv0, mul_mem B.2 hR⟩ *
          matrixIsometryInclusion (coordinateQuadPlus 4 K)
            ⟨reflMat _ (OmegaPilot.plusUnitVector hn) hv0, hR⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change B.val = B.val * reflMat _ (OmegaPilot.plusUnitVector hn) hv0 *
        reflMat _ (OmegaPilot.plusUnitVector hn) hv0
      rw [mul_assoc, reflMat_mul_self, mul_one]
    refine ⟨_, conjAct_inclusion_mem_inner (Q := coordinateQuadPlus 4 K)
      ⟨B.val * reflMat _ (OmegaPilot.plusUnitVector hn) hv0, mul_mem B.2 hR⟩ hBΓ, _,
      ⟨σ, Or.inr rfl⟩, ?_⟩
    rw [hα, hιB, map_mul, mul_assoc]
    rfl

theorem exists_pair_of_mem_plusCompl {c : MulAut (Om8 K)}
    (hc : c ∈ AutOm.plusCompl (K := K) one_le_four) :
    ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = c := by
  obtain ⟨σ, rfl | rfl⟩ := hc
  · exact ⟨_, (AutOm.fieldAutP_eq σ).symm⟩
  · exact ⟨_, (AutOm.plusRefl_mul_fieldAutP_eq one_le_four σ).symm⟩

omit [Finite K] [CharP K 2] in
theorem exists_pair_of_mem_inner {ι : MulAut (Om8 K)} (hι : ι ∈ inner (Om8 K)) :
    ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = ι := by
  obtain ⟨γ, rfl⟩ := hι
  exact ⟨_, conjAct_inclusion_of_mem ⟨γ.val, matrixDerived_le_isometries _ γ.2⟩ γ.2⟩

end Pair

section Main

variable [Finite K] [CharP K 2]

theorem theta_smul_pointFamily_ne :
    MulAut.congr projEquiv8 (theta : MulAut (Om8 K)) •
        projectivePointFamily (coordinateQuadPlus 4 K) ≠
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  intro h
  have hmem := (mem_projectivePointFamilyAut_iff _ _).2 h
  rw [pointFamilyAut_eq_image] at hmem
  obtain ⟨g, hg⟩ := exists_pair_of_mem_image hmem
  exact conjAct_ne_theta g hg

theorem theta_inv_smul_pointFamily_ne :
    (MulAut.congr projEquiv8 (theta : MulAut (Om8 K)))⁻¹ •
        projectivePointFamily (coordinateQuadPlus 4 K) ≠
      projectivePointFamily (coordinateQuadPlus 4 K) := by
  intro h
  have hmem := (mem_projectivePointFamilyAut_iff _ _).2 h
  rw [pointFamilyAut_eq_image, ← map_inv] at hmem
  obtain ⟨g, hg⟩ := exists_pair_of_mem_image hmem
  exact conjAct_ne_theta_inv g hg

theorem exists_pow_smul_pointFamily
    (a : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
    ∃ k : ℕ, a • projectivePointFamily (coordinateQuadPlus 4 K) =
      MulAut.congr projEquiv8 (theta : MulAut (Om8 K)) ^ k •
        projectivePointFamily (coordinateQuadPlus 4 K) := by
  set t := MulAut.congr projEquiv8 (theta : MulAut (Om8 K))
  set F := projectivePointFamily (coordinateQuadPlus 4 K)
  have ht3 : t ^ 3 = 1 := by rw [← map_pow, theta_cube, map_one]
  have ht2 : t ^ 2 = t⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, ht3])
  have h1 : t • F ≠ F := theta_smul_pointFamily_ne
  have h2 : t⁻¹ • F ≠ F := theta_inv_smul_pointFamily_ne
  have h12 : t • F ≠ t⁻¹ • F := by
    intro h
    apply h2
    have h' := congrArg (t • ·) h
    simp only [smul_smul, mul_inv_cancel, one_smul] at h'
    rwa [← sq, ht2] at h'
  rcases smul_pointFamily_cases a with ha | ha | ha
  · exact ⟨0, by rw [ha, pow_zero, one_smul]⟩
  · rcases smul_pointFamily_cases t with hx | hx | hx
    · exact absurd hx h1
    · exact ⟨1, by rw [ha, pow_one, hx]⟩
    · rcases smul_pointFamily_cases t⁻¹ with hy | hy | hy
      · exact absurd hy h2
      · exact ⟨2, by rw [ha, ht2, hy]⟩
      · exact absurd (hx.trans hy.symm) h12
  · rcases smul_pointFamily_cases t with hx | hx | hx
    · exact absurd hx h1
    · rcases smul_pointFamily_cases t⁻¹ with hy | hy | hy
      · exact absurd hy h2
      · exact absurd (hx.trans hy.symm) h12
      · exact ⟨2, by rw [ha, ht2, hy]⟩
    · exact ⟨1, by rw [ha, pow_one, hx]⟩

theorem exists_inner_mul_theta_pow_mul (α : MulAut (Om8 K)) :
    ∃ ι ∈ inner (Om8 K), ∃ k : ℕ, ∃ c ∈ AutOm.plusCompl (K := K) one_le_four,
      α = ι * (theta ^ k * c) := by
  obtain ⟨k, hk⟩ := exists_pow_smul_pointFamily (MulAut.congr projEquiv8 α)
  have hmem : MulAut.congr projEquiv8 ((theta ^ k)⁻¹ * α) ∈
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rw [← pointFamilyAut_eq_image, map_mul, map_inv, map_pow]
    have h' : ((MulAut.congr projEquiv8 (theta : MulAut (Om8 K)) ^ k)⁻¹ *
        MulAut.congr projEquiv8 α) • projectivePointFamily (coordinateQuadPlus 4 K) =
          projectivePointFamily (coordinateQuadPlus 4 K) := by
      rw [mul_smul, hk, inv_smul_smul]
    exact (mem_projectivePointFamilyAut_iff _ _).2 h'
  obtain ⟨g, hg⟩ := exists_pair_of_mem_image hmem
  obtain ⟨ι, hι, c, hc, hgc⟩ := exists_inner_mul_plusCompl_of_pair g
  refine ⟨theta ^ k * ι * (theta ^ k)⁻¹, (inner_normal _).conj_mem ι hι _, k, c, hc, ?_⟩
  calc α = theta ^ k * ((theta ^ k)⁻¹ * α) := by rw [mul_inv_cancel_left]
    _ = theta ^ k * (ι * c) := by rw [← hg, hgc]
    _ = theta ^ k * ι * (theta ^ k)⁻¹ * (theta ^ k * c) := by group

theorem theta_pow_mul_mem_inner (k : ℕ) {c : MulAut (Om8 K)}
    (hc : c ∈ AutOm.plusCompl (K := K) one_le_four) (h : theta ^ k * c ∈ inner (Om8 K)) :
    (theta : MulAut (Om8 K)) ^ k = 1 ∧ c = 1 := by
  obtain ⟨gc, hgc⟩ := exists_pair_of_mem_plusCompl hc
  obtain ⟨gι, hgι⟩ := exists_pair_of_mem_inner h
  have hk : (theta : MulAut (Om8 K)) ^ k = conjAct _ (gι * gc⁻¹) := by
    rw [map_mul, map_inv, hgι, hgc, mul_inv_cancel_right]
  have h1 := theta_pow_eq_one_of_eq_conjAct hk
  refine ⟨h1, ?_⟩
  rw [h1, one_mul] at h
  have hc' : c ∈ inner (Om8 K) ⊓ AutOm.plusCompl (K := K) one_le_four := ⟨h, hc⟩
  rw [AutOm.inner_inf_plusCompl (K := K) (n := 4) (by norm_num)] at hc'
  exact hc'

theorem _root_.CFSG.StandardType.plusFourTrialityInput_holds : PlusFourTrialityInput := by
  intro K _ _ _
  exact ⟨theta, theta_cube, plusRefl_theta_plusRefl, theta_fieldAutP,
    exists_inner_mul_theta_pow_mul, fun k c hc h => theta_pow_mul_mem_inner k hc h,
    fun r hr => theta_plusRootElt hr⟩

end Main

end Triality

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal

theorem ggAutModelPlusFourInput_holds : GGAutModelPlusFourInput :=
  plusFourInput_of_triality plusFourTrialityInput_holds

theorem ggAutModelAt_POmegaPlus : GGAutModelAt .POmegaPlus :=
  ggAutModelAt_POmegaPlus_of_triality plusFourTrialityInput_holds

theorem ggAutStructureAt_POmegaPlus : GGAutStructureAt .POmegaPlus :=
  ggAutStructureAt_POmegaPlus_of_triality plusFourTrialityInput_holds

end Family

end CFSG.StandardType
