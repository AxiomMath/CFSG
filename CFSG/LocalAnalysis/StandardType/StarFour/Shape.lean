module

public import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

private lemma image_eq_map_subgroupOf {G : Type*} [Group G] (B D : Subgroup X) (hat : B →* G)
    (hD : D ≤ B) (g : X → G) (hg : ∀ x (hx : x ∈ D), g x = hat ⟨x, hD hx⟩) :
    g '' (D : Set X) = ((D.subgroupOf B).map hat : Set G) := by
  ext y
  constructor
  · rintro ⟨b, hb, hby⟩
    exact ⟨⟨b, hD hb⟩, hb, (hg b hb).symm.trans hby⟩
  · rintro ⟨b, hb, hby⟩
    have hhat : g (b : X) = hat b :=
      (hg (b : X) hb).trans (congrArg hat (Subtype.ext rfl))
    exact ⟨(b : X), hb, hhat.trans hby⟩

theorem exists_frame_of_component [Finite X] (ψ : SpecialLinearGroup F V →* X)
    (hψ : Function.Injective ψ) (B₁ D J : Subgroup X) (hat : B₁ →* SpecialLinearGroup F V)
    (hhat : ∀ (b : B₁) (u : SpecialLinearGroup F V),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹))
    (hD : D ≤ B₁) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDodd : (Nat.card D : F) ≠ 0)
    (hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X))) :
    ∃ (P : Type) (_ : CommGroup P) (η : P →* SpecialLinearGroup F V)
      (fr : SemiFrame F (groupRep η)) (i : Fin fr.r),
      η.range = (D.subgroupOf B₁).map hat ∧ fr.GoodAtBlock i ∧ J = (fr.slOnBlock i).map ψ := by
  classical
  let P : Type := ↥(D.subgroupOf B₁)
  let inst : CommGroup P :=
    { (inferInstance : Group P) with
      mul_comm := fun a b =>
        Subtype.ext (Subtype.ext (hDab (a.1.1 : X) a.2 (b.1.1 : X) b.2)) }
  letI : CommGroup P := inst
  let η : P →* SpecialLinearGroup F V := hat.comp (D.subgroupOf B₁).subtype
  let hat' : X → SpecialLinearGroup F V :=
    fun x => if h : x ∈ B₁ then hat ⟨x, h⟩ else 1
  have hηrange : η.range = (D.subgroupOf B₁).map hat := by
    show (hat.comp (D.subgroupOf B₁).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hPcard : Nat.card P = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv
  have hP : (Nat.card P : F) ≠ 0 := by
    rw [hPcard]
    exact hDodd
  obtain ⟨fr⟩ := exists_semiFrame hP (groupRep η)
  have hS : ∀ b ∈ (D : Set X), ∀ u : SpecialLinearGroup F V,
      b * ψ u * b⁻¹ = ψ (hat' b * u * (hat' b)⁻¹) := by
    intro b hb u
    have hbB : b ∈ B₁ := hD hb
    have hhatb : hat' b = hat ⟨b, hbB⟩ := by
      change (if h : b ∈ B₁ then hat ⟨b, h⟩ else 1) = hat ⟨b, hbB⟩
      rw [dif_pos hbB]
    rw [hhatb]
    exact hhat ⟨b, hbB⟩ u
  have hset : hat' '' (D : Set X) =
      ((D.subgroupOf B₁).map hat : Set (SpecialLinearGroup F V)) := by
    refine image_eq_map_subgroupOf B₁ D hat hD hat' fun x hx => ?_
    change (if h : x ∈ B₁ then hat ⟨x, h⟩ else 1) = hat ⟨x, hD hx⟩
    rw [dif_pos (hD hx)]
  have hcent : Subgroup.centralizer (hat' '' (D : Set X)) = repCentSL (groupRep η) := by
    rw [hset, ← hηrange]
    exact (repCentSL_groupRep η).symm
  have hinf : ψ.range ⊓ Subgroup.centralizer (D : Set X) =
      (repCentSL (groupRep η)).map ψ := by
    rw [inf_centralizer_eq_map_centralizer ψ hψ (D : Set X) hat' hS, hcent]
  have hcomp : IsComponentOf (J.comap ψ) (repCentSL (groupRep η)) := by
    have h1 := CFSG.ComponentClassification.OddClassSelector.isComponentOf_comap_of_le_range
      ψ hψ hJ inf_le_left
    rw [hinf] at h1
    rw [Subgroup.comap_map_eq_self_of_injective hψ] at h1
    exact h1
  obtain ⟨i, hgood, hK⟩ := SemiFrame.exists_eq_slOnBlock_of_isComponentOf fr hcomp
  refine ⟨P, inst, η, fr, i, hηrange, hgood, ?_⟩
  have hJle : J ≤ ψ.range := hJ.1.trans inf_le_left
  have hmap : (J.comap ψ).map ψ = J := Subgroup.map_comap_eq_self hJle
  rw [hK] at hmap
  exact hmap.symm

end CFSG.StandardType.StarFour
