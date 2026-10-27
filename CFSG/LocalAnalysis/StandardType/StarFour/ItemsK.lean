module

public import CFSG.LocalAnalysis.StandardType.StarFour.ItemsFrames
public import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
import CFSG.HardMathSupport.Timmesfeld.Proving.ComponentCentralizer
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

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open
open scoped IsMulCommutative

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

private theorem range_inf_centralizer_singleton
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (B₁ : Subgroup X)
    (hat : B₁ →* SpecialLinearGroup F V)
    (hhat : ∀ (b : B₁) (u : SpecialLinearGroup F V),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹))
    {e : X} (heB : e ∈ B₁) :
    ψ.range ⊓ Subgroup.centralizer {e} =
      (Subgroup.centralizer {hat ⟨e, heB⟩}).map ψ := by
  classical
  let hatX : X → SpecialLinearGroup F V :=
    fun x => if h : x ∈ B₁ then hat ⟨x, h⟩ else 1
  have hhatXe : hatX e = hat ⟨e, heB⟩ := by
    simp only [hatX, dif_pos heB]
  have hS : ∀ b ∈ ({e} : Set X), ∀ u : SpecialLinearGroup F V,
      b * ψ u * b⁻¹ = ψ (hatX b * u * (hatX b)⁻¹) := by
    intro b hb u
    rw [Set.mem_singleton_iff] at hb
    subst b
    rw [hhatXe]
    exact hhat ⟨e, heB⟩ u
  have h := inf_centralizer_eq_map_centralizer ψ hψ ({e} : Set X) hatX hS
  rwa [Set.image_singleton, hhatXe] at h

theorem rootInnerNoCentral_of_component {P : Type} [CommGroup P]
    (η : P →* SpecialLinearGroup F V) (fr : SemiFrame F (groupRep η)) (i : Fin fr.r)
    (hm : 3 ≤ fr.m i) (hc : 2 ≤ Module.finrank F (fr.E i))
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (B₁ D : Subgroup X)
    (hat : B₁ →* SpecialLinearGroup F V)
    (hhat : ∀ (b : B₁) (u : SpecialLinearGroup F V),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹))
    (hDB : D ≤ B₁) (hDη : η.range = (D.subgroupOf B₁).map hat) (hDodd : Odd (Nat.card D)) :
    ∀ e ∈ D, ∀ K : Subgroup X, K ≤ ψ.range →
      CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) →
      (fr.slOnBlock i).map ψ ≤ K → K ≠ (fr.slOnBlock i).map ψ →
        GGRootInnerAt K ((fr.blockRoot i (by omega)).map ψ) ∧
          GGRootNoCentralAt K ((fr.blockRoot i (by omega)).map ψ) := by
  intro e he K hKG hKc hJK hKJ
  let ê : SpecialLinearGroup F V := hat ⟨e, hDB he⟩
  have hinf : ψ.range ⊓ Subgroup.centralizer {e} = (Subgroup.centralizer {ê}).map ψ :=
    range_inf_centralizer_singleton ψ hψ B₁ hat hhat (hDB he)
  have hKc' : CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e} ⊓ ψ.range) :=
    CFSG.Assembly.isComponentOf_iff_open.2
      (CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le
        (CFSG.Assembly.isComponentOf_iff_open.1 hKc) hKG)
  have hKc'' : CFSG.Assembly.IsComponentOf (K.comap ψ)
      ((Subgroup.centralizer {e} ⊓ ψ.range).comap ψ) :=
    CFSG.ComponentClassification.OddClassSelector.isComponentOf_comap_of_le_range
      ψ hψ hKc' inf_le_right
  have hcomap : (Subgroup.centralizer {e} ⊓ ψ.range).comap ψ =
      Subgroup.centralizer {ê} := by
    rw [inf_comm, hinf, Subgroup.comap_map_eq_self_of_injective hψ]
  have hKc₀ : CFSG.Assembly.IsComponentOf (K.comap ψ) (Subgroup.centralizer {ê}) :=
    hcomap ▸ hKc''
  have hKmap : (K.comap ψ).map ψ = K := Subgroup.map_comap_eq_self hKG
  haveI : Finite V :=
    Finite.of_injective ((Module.finBasis F V).equivFun : V → (Fin (Module.finrank F V) → F))
      (Module.finBasis F V).equivFun.injective
  haveI : Finite (SpecialLinearGroup F V) :=
    Finite.of_injective (fun u : SpecialLinearGroup F V => (u : V → V))
      (fun u v h => by ext x; exact congrFun h x)
  let P' : Type := ↥(Subgroup.zpowers ê)
  letI : CommGroup P' := inferInstance
  haveI : Finite P' :=
    Finite.of_injective (Subtype.val : P' → SpecialLinearGroup F V) Subtype.val_injective
  let η' : P' →* SpecialLinearGroup F V := (Subgroup.zpowers ê).subtype
  have horder : orderOf ê ∣ Nat.card D := by
    have h1 : orderOf ê ∣ orderOf (⟨e, hDB he⟩ : B₁) := orderOf_map_dvd hat ⟨e, hDB he⟩
    rw [Subgroup.orderOf_mk e (hDB he)] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard D he)
  have hodd : Odd (orderOf ê) := Odd.of_dvd_nat hDodd horder
  have hcard : (Nat.card P' : F) ≠ 0 := by
    have hP : Nat.card P' = orderOf ê := Nat.card_zpowers ê
    rw [hP]
    intro h0
    have h2 : 2 ∣ orderOf ê := (CharP.cast_eq_zero_iff F 2 (orderOf ê)).mp h0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨fr'⟩ : Nonempty (SemiFrame F (groupRep η')) :=
    exists_semiFrame hcard (groupRep η')
  have hrange : η'.range = Subgroup.zpowers ê := Subgroup.range_subtype (Subgroup.zpowers ê)
  have hrep : repCentSL (groupRep η') = Subgroup.centralizer {ê} := by
    rw [repCentSL_groupRep, hrange, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hK₀ : CFSG.Assembly.IsComponentOf (K.comap ψ) (repCentSL (groupRep η')) := by
    rwa [hrep]
  obtain ⟨i', hgood, hK₀eq⟩ := SemiFrame.exists_eq_slOnBlock_of_isComponentOf fr' hK₀
  have hKeq : K = (fr'.slOnBlock i').map ψ :=
    hKmap.symm.trans (congrArg (Subgroup.map ψ) hK₀eq)
  have hle : fr.slOnBlock i ≤ fr'.slOnBlock i' :=
    (Subgroup.map_le_map_iff_of_injective hψ).mp (by rwa [hKeq] at hJK)
  have hne : fr'.slOnBlock i' ≠ fr.slOnBlock i := by
    intro heq
    exact hKJ (by rw [hKeq, heq])
  have hê_mem : ê ∈ η.range := by
    rw [hDη]
    exact Subgroup.mem_map.mpr ⟨⟨e, hDB he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hê_mem
  let g' : P' := ⟨ê, Subgroup.mem_zpowers ê⟩
  have hg' : ∀ x : P', x ∈ Subgroup.zpowers g' := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hk
  have hgg : η' g' = η g := by
    rw [hg]
    rfl
  have hres := items_of_frames η η' hg' hgg fr fr' i hm hc i' hle hne ψ hψ
  rw [hKeq]
  refine ⟨?_, ?_⟩
  · convert hres.1 using 1
  · convert hres.2 using 1

end CFSG.StandardType.StarFour
