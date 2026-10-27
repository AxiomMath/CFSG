module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockModels
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import CFSG.RankThree.PartOne.S15K.BlockType
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
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
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate116
import Certificates.Certificate119
import Certificates.Certificate122
import Certificates.Certificate123
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.Assembly.LowTwoRank (StatedClassicalModel specialLinearGroupEquivStatedSL)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem ggTBJD4_model_specialBlock (hx : OddOrderIsometry Q p x) {μ : K}
    (hh : X - C μ ∈ primaryFactors x.toLinearMap)
    (hne : X - C μ ≠ reciprocalPolynomial (X - C μ))
    (hm : primaryMultiplicity x.toLinearMap (X - C μ) = 4) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {J : Type} [Group J] (e : J ≃* ↥(specialBlock Q x (X - C μ))) :
    StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 4 2 f := by
  have : Fact (Irreducible (X - C μ)) := ⟨irreducible_X_sub_C μ⟩
  obtain ⟨e₁⟩ := hx.nonempty_specialBlock_mulEquiv_SL_paired hh hne
  rw [hm] at e₁
  have hE : Nat.card (AdjoinRoot (X - C μ)) = 2 ^ f := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, natDegree_X_sub_C, pow_one, hK]
  exact CFSG.RankThree.PartOne.S15K.statedClassicalModel_psl_of_sl hE hf (by norm_num)
    (e.trans e₁)

theorem ggTBJD4_model_fixed [CharP K 2] (hx : OddOrderIsometry Q p x)
    (hd : finrank K (fixedSpace x) = 6)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {J : Type} [Group J] (e : J ≃* ↥(supportedFixedDerived Q x)) :
    StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 4 2 f := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate hd hT h4
  exact CFSG.RankThree.PartOne.S15K.statedClassicalModel_psl_of_sl hK hf (by norm_num)
    (e.trans ((supportedFixedDerivedEquiv hx).trans
      ((CFSG.RankThree.PartOne.orthDerivedEquivCommutator _).symm.trans
        (κ.trans (specialLinearGroupEquivStatedSL 4 K).symm))))

end CFSG.StandardType

end
