module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOrthBlock
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOrthSpecial
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOrthPaired
import CFSG.LocalAnalysis.StandardType.GGLieSU3FixedOrthSelfDual
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4Twin
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.Walter.ReeOrder.JT.Defs
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.Classical2
open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

theorem ggLieSU3Fixed_orth_core {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (E : Set ↥(orthDerived Q)) (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) {d : ↥(orthDerived Q)} (hdE : d ∈ E)
    (Jh : Subgroup ↥(orthDerived Q))
    (hJ : CFSG.Assembly.IsComponentOf Jh
      (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))))
    {z : ↥(orthDerived Q)} (hzJ : z ∈ Jh) (hzc : ∀ j ∈ Jh, z * j = j * z) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hzE : ∀ x ∈ E, z * x = x * z) :
    ∃ t ∈ Jh, (∀ x ∈ E, t * x = x * t) ∧ ∃ u ∈ Jh, t * u ≠ u * t := by
  classical
  let f : ↥(orthDerived Q) →* (V ≃ₗ[K] V) := (orthDerived Q).subtype
  let D : Subgroup (V ≃ₗ[K] V) := Jh.map f
  have hker_eq : f.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff f).mpr (Subgroup.subtype_injective (orthDerived Q))
  have hker : f.ker ≤ Subgroup.center ↥(orthDerived Q) :=
    le_trans (le_of_eq hker_eq) bot_le
  have hmap_cent : (Subgroup.centralizer ({d} : Set ↥(orthDerived Q))).map f =
      orthDerived Q ⊓ Subgroup.centralizer ({(d : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨s, hs, rfl⟩ := hg
      refine Subgroup.mem_inf.mpr ⟨s.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hs ⊢
      change (s : V ≃ₗ[K] V) * (d : V ≃ₗ[K] V) = (d : V ≃ₗ[K] V) * (s : V ≃ₗ[K] V)
      simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) hs
    · intro hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgO, hgc⟩ := hg
      rw [Subgroup.mem_map]
      refine ⟨⟨g, hgO⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
      exact Subtype.ext (by simpa using hgc)
  have hD : CFSG.Assembly.IsComponentOf D
      (orthDerived Q ⊓ Subgroup.centralizer ({(d : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) := by
    have h :=
      CFSG.ComponentClassification.HarrisLit.N36.isComponentOf_map_of_ker_le_center f hker hJ
    rw [hmap_cent] at h
    exact h
  have hd3' : (d : V ≃ₗ[K] V) ^ 3 = 1 := by
    simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hE3 d hdE)
  have hz3' : (z : V ≃ₗ[K] V) ^ 3 = 1 := by
    simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) hz3
  have hz1' : (z : V ≃ₗ[K] V) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzD' : (z : V ≃ₗ[K] V) ∈ D := by
    change (z : V ≃ₗ[K] V) ∈ Jh.map f
    exact Subgroup.mem_map_of_mem f hzJ
  have hzc' : ∀ g ∈ D, (z : V ≃ₗ[K] V) * g = g * (z : V ≃ₗ[K] V) := by
    intro g hg
    change g ∈ Jh.map f at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    change (z : V ≃ₗ[K] V) * (g₀ : V ≃ₗ[K] V) = (g₀ : V ≃ₗ[K] V) * (z : V ≃ₗ[K] V)
    simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hzc g₀ hg₀)
  obtain ⟨y, hy, j, hj, hj1, hsub⟩ :=
    ggLieSU3Fixed_exists_block hQ d.2 hd3' hz3' hz1' hD hzD' hzc'
  have hydz : y = (d : V ≃ₗ[K] V) ∨ y = (z : V ≃ₗ[K] V) := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
  have h3K : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hdO' : (d : V ≃ₗ[K] V) ∈ orthDerived Q := d.2
  have hyO : y ∈ orthDerived Q := by
    rcases hydz with hy | hy
    · rw [hy]; exact hdO'
    · rw [hy]; exact z.2
  have hy3 : y ^ 3 = 1 := by
    rcases hydz with hy | hy
    · rw [hy]; exact hd3'
    · rw [hy]; exact hz3'
  have hye : OddOrderIsometry Q 3 y :=
    ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hyO, hy3, h3K, fun v hv =>
      hQ.1 v fun w => by simpa [QuadraticMap.polarBilin_apply_apply] using hv w⟩
  have hDq : CFSG.Assembly.IsQuasisimple ↥D := hD.2.2
  obtain ⟨hDsb, hm2⟩ := ggLieSU3Fixed_eq_specialBlock hye hj hj1 hsub hDq
  let E' : Set (V ≃ₗ[K] V) := (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[K] V)) '' E
  have hEy : E' ⊆ isometryCentralizer Q y := by
    rintro g ⟨x, hxE, rfl⟩
    refine Subgroup.mem_inf.mpr
      ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hydz with hy | hy
    · rw [hy]
      simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hEc x hxE d hdE)
    · rw [hy]
      simpa using (congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hzE x hxE)).symm
  have hEc' : ∀ x ∈ E', ∀ x' ∈ E', x * x' = x' * x := by
    rintro x ⟨x₀, hx₀, rfl⟩ x' ⟨x₁, hx₁, rfl⟩
    simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hEc x₀ hx₀ x₁ hx₁)
  have hE3' : ∀ x ∈ E', x ^ 3 = 1 := by
    rintro x ⟨x₀, hx₀, rfl⟩
    simpa using congrArg (fun t : ↥(orthDerived Q) => (t : V ≃ₗ[K] V)) (hE3 x₀ hx₀)
  have htorus : ∃ t ∈ specialBlock Q y j, (∀ x ∈ E', t * x = x * t) ∧
      ∃ u ∈ specialBlock Q y j, t * u ≠ u * t := by
    by_cases hjs : j = reciprocalPolynomial j
    · exact ggLieSU3Fixed_torus_selfDual hye hj hj1 hjs hm2 E' hEy hEc' hE3'
    · exact ggLieSU3Fixed_torus_paired hye hj hj1 hjs hm2 E' hEy hEc' hE3'
  obtain ⟨t, ht, htcen, u, hu, htu⟩ := htorus
  have htD : t ∈ D := by rw [hDsb]; exact ht
  have huD : u ∈ D := by rw [hDsb]; exact hu
  change t ∈ Jh.map f at htD
  rw [Subgroup.mem_map] at htD
  obtain ⟨t₀, ht₀J, ht₀eq⟩ := htD
  change u ∈ Jh.map f at huD
  rw [Subgroup.mem_map] at huD
  obtain ⟨u₀, hu₀J, hu₀eq⟩ := huD
  have ht₀' : (t₀ : V ≃ₗ[K] V) = t := ht₀eq
  have hu₀' : (u₀ : V ≃ₗ[K] V) = u := hu₀eq
  refine ⟨t₀, ht₀J, ?_, u₀, hu₀J, ?_⟩
  · intro x hxE
    apply Subtype.ext
    have hxE' : (x : V ≃ₗ[K] V) ∈ E' := ⟨x, hxE, rfl⟩
    have hct := htcen (x : V ≃ₗ[K] V) hxE'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ht₀']
    exact hct
  · intro h
    apply htu
    have hc := congrArg (fun s : ↥(orthDerived Q) => (s : V ≃ₗ[K] V)) h
    simpa [Subgroup.coe_mul, ht₀', hu₀'] using hc

end CFSG.StandardType
