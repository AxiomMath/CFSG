module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdStandard
public import CFSG.LocalAnalysis.StandardType.GGE6DepFixedNoncentral
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.GGE6Dep

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem isComponentOf_inf_centralizer_of_unique {C M D : Subgroup G} {S : Set G}
    (hM : IsComponentOf M C) (hSM : S ⊆ (M : Set G))
    (hnc : ∃ s ∈ S, ∃ m ∈ M, m * s ≠ s * m)
    (hD : IsComponentOf D (M ⊓ Subgroup.centralizer S))
    (huniq : ∀ D' : Subgroup G, IsComponentOf D' (M ⊓ Subgroup.centralizer S) → D' = D) :
    IsComponentOf D (C ⊓ Subgroup.centralizer S) := by
  obtain ⟨s, hsS, m, hmM, hms⟩ := hnc
  have hsM : s ∈ M := hSM hsS
  have hnsM : ∃ l ∈ M, l * s ≠ s * l := ⟨m, hmM, hms⟩
  have hXD : (C ⊓ Subgroup.centralizer S : Subgroup G) ≤
      Subgroup.normalizer (D : Set G) := by
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyC, hyS⟩ := hy
    have hsy : y * s * y⁻¹ = s := by
      have h := (Subgroup.mem_centralizer_iff.mp hyS) s hsS
      calc y * s * y⁻¹ = s * y * y⁻¹ := by rw [← h]
        _ = s := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have hyM : y ∈ Subgroup.normalizer (M : Set G) :=
      normalizes_of_fixed_noncentral hM (Subgroup.le_normalizer hyC) hsM hnsM hsy
    have hmap : (M ⊓ Subgroup.centralizer S).map (MulAut.conj y).toMonoidHom =
        M ⊓ Subgroup.centralizer S := by
      rw [Subgroup.map_inf M (Subgroup.centralizer S) (MulAut.conj y).toMonoidHom
          (MulAut.conj y).injective,
        map_conj_eq_of_mem_normalizer hyM, map_conj_eq_of_mem hyS]
    have hDy : IsComponentOf (D.map (MulAut.conj y).toMonoidHom)
        (M ⊓ Subgroup.centralizer S) := by
      rw [← hmap]
      exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hD y
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hDy)
  have hDX : D ≤ C ⊓ Subgroup.centralizer S := by
    intro d hd
    exact ⟨hM.1 (hD.1 hd).1, (hD.1 hd).2⟩
  exact CFSG.ComponentClassification.RestrictedStd.isComponentOf_of_normal
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥D).1 hD.2.2)
    hDX hXD

end CFSG.StandardType.GGE6Dep

end
