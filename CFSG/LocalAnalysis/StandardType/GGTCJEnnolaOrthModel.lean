module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsDomain
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate116
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate123
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow

theorem exists_projOrth_model_type {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {G : Type} [Group G] {m f : ℕ} (hG : StatedClassicalModel G t m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (Q : QuadraticForm K V),
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      Nat.card K = 2 ^ f ∧ Module.finrank K V = 2 * m ∧
      (IsPlusType Q ↔ t = .POmegaPlus) ∧ Nonempty (G ≃* ProjOrthDerived Q) := by
  rcases ht with rfl | rfl
  · obtain ⟨hadm, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ m := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m)
      (by omega)
    refine ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard, ?_,
      iff_of_true (isPlusType_quadPlus K m) rfl,
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadPlus (n := m) (K := K)))⟩⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  · obtain ⟨hadm, K, hKf, hKfin, hcard, b, c, hirr, ⟨e⟩⟩ := hG
    have h4 : 4 ≤ m := hadm.2.2
    obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := m) h4 hirr
    refine ⟨K, hKf, hKfin, _, inferInstance, inferInstance, inferInstance, _, hQ, hT, hcard, ?_,
      iff_of_false (not_isPlusType_quadMinus (by omega) hirr) (fun h => by cases h),
      ⟨e.trans (CFSG.RankThree.PartOne.statedProjOrthEquiv
        (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c))⟩⟩
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega

end CFSG.StandardType.TCJ

end
