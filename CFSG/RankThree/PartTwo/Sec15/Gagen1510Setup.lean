module

public import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_mulEquiv {X : Type*} [Group X]
    (χ : X ≃* projSL 3 (GaloisField 2 2)) : Subgroup.center X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := Subgroup.map_center_eq χ
  rw [(isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)).2] at hZ
  exact (Subgroup.map_eq_bot_iff_of_injective _ χ.injective).mp hZ

theorem setting {A L : Subgroup G} {c : G} (h : Sec15R G A c L) (hall : All1510 A) :
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) ∧
      Nat.card (A ⊓ L : Subgroup G) = 9 ∧ c ∉ L ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hD := h.toSec13Data
  obtain ⟨⟨χ⟩, h9⟩ := Proof1510.facts_l34_of_quot hD (hall c L hD.mem_lA hD.zpowers_mem_omegaA)
  have hcL : c ∉ L := by
    intro hc
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) (⟨c, hc⟩ : ↥L) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) z
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer ℓ.2))
    rw [center_eq_bot_of_mulEquiv χ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hcen
    have hθ : c ∈ Subgroup.zpowers c ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
      ⟨Subgroup.mem_zpowers c, ⟨⟨c, hc⟩, hcen, rfl⟩⟩
    have h3 : IsPGroup 3 (Subgroup.zpowers c) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.of_card (n := 1) (by rw [hD.card_zpowers, pow_one])
    rw [Proof1510Steps.inf_eq_bot_of_coprime h3 (Proof1510Steps.not_three_dvd_card_theta L),
      Subgroup.mem_bot] at hθ
    exact hD.ne_one hθ
  refine ⟨⟨χ⟩, h9, hcL, eq_sup_of_card_nine hD h9 fun hc => hcL hc.2, ?_⟩
  exact centralizer_le_normalizer_of_three_dvd h.toSec14Std
    (three_dvd_card_of_thetaQuot χ (by rw [KFacts.KS14.card_projSL_three_four]; norm_num))

theorem thetaQuotMulAut_eq_one_iff {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hg⟩) = 1 ↔
      ∀ ℓ ∈ L, g * ℓ * g⁻¹ * ℓ⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have key : ∀ ℓ : ↥L, (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hg⟩)
      (ℓ : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = (ℓ : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ↔
        g * ℓ * g⁻¹ * (ℓ : G)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) := by
    intro ℓ
    rw [Sec4.thetaQuotMulAut_mk, QuotientGroup.eq]
    set m : ↥L := L.normalizerMonoidHom ⟨g, hg⟩ ℓ with hm
    have hmc : (m : G) = g * ℓ * g⁻¹ := Sec4.normalizerMonoidHom_apply_coe hg ℓ
    constructor
    · intro hmem
      have h2 : m * (m⁻¹ * ℓ) * m⁻¹ ∈ aschbacherSolvableCore 3 ↥L :=
        (inferInstance : (aschbacherSolvableCore 3 ↥L).Normal).conj_mem _ hmem m
      refine ⟨(m * (m⁻¹ * ℓ) * m⁻¹)⁻¹, inv_mem h2, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, hmc]
      group
    · rintro ⟨w, hw, hwe⟩
      have h2 : m⁻¹ * w⁻¹ * m ∈ aschbacherSolvableCore 3 ↥L := by
        have := (inferInstance : (aschbacherSolvableCore 3 ↥L).Normal).conj_mem _
          (inv_mem hw) m⁻¹
        simpa only [inv_inv] using this
      convert h2 using 1
      apply Subtype.ext
      have hw' : (w : G) = g * ℓ * g⁻¹ * (ℓ : G)⁻¹ := hwe
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, hmc, hw']
      group
  constructor
  · intro h1 ℓ hℓ
    have := congrArg (fun φ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) =>
      φ ((⟨ℓ, hℓ⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) h1
    exact (key ⟨ℓ, hℓ⟩).mp this
  · intro h1
    ext z
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective z
    exact (key ℓ).mpr (h1 ℓ ℓ.2)

theorem mem_sectionCentralizer_iff {P L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) ↔
      g ∈ P ∧ Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨g, hg⟩) = 1 := by
  rw [thetaQuotMulAut_eq_one_iff hg]
  rfl

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
