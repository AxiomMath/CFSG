module

public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUSporadic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUMathieuVanishing
public meta import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Certificate2335
public import Certificates.Certificate1020
public import Certificates.Certificate1021
public import Certificates.Certificate1022
public import Certificates.Certificate2309
public import Certificates.Certificate2311
public import Certificates.Certificate2313
public import Certificates.Certificate2314
public import Certificates.Certificate2315
public import Certificates.Certificate2317
public import Certificates.Certificate2321
public import Certificates.Certificate2322
public import Certificates.Certificate2323
public import Certificates.Certificate2324
public import Certificates.Certificate2325
public import Certificates.Certificate10088
public import Certificates.Certificate10089
public import Certificates.Certificate10090
public import Certificates.Certificate10091
public import Certificates.Certificate10092
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.ComponentClassification.OuterAutomorphisms Subgroup

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
private theorem native_ab_ne_ba : eqRows (mulRows rowsA rowsB) (mulRows rowsB rowsA) = false :=
  Certificates.certificate2335

open CFSG.Sporadic.Th.Max3 in
theorem ab_ne_ba : a * b ≠ b * a :=
  (isRows_a.mul isRows_b).ne_of_eqRows (isRows_b.mul isRows_a) native_ab_ne_ba

theorem th_not_comm : ∃ x y : Blueprint.NativeSporadic.Th, x * y ≠ y * x := by
  refine ⟨thEquivJ.symm a, thEquivJ.symm b, fun h => ab_ne_ba ?_⟩
  have := congrArg thEquivJ h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem ctuc_Th_generalized_Fitting_involution_centralizer_exclusion {X : Type} [Group X]
    [Finite X] (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.Th)) :
    CFSG.generalizedFitting X = ⊤ ∧
      ∀ t : X, orderOf t = 2 → CFSG.oddCore (centralizer ({t} : Set X)) = ⊥ := by
  have hFn : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨ψ⟩ := hJ
  have hnab : ∃ x y : CFSG.generalizedFitting X, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := th_not_comm
    refine ⟨ψ.symm x, ψ.symm y, fun h => hxy ?_⟩
    have := congrArg ψ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  have hC : centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
    CFSG.ComponentClassification.CatalogueU.centralizer_generalizedFitting_eq_bot_of_simple hF
      hnab
  have hinner : inner (CFSG.generalizedFitting X) = ⊤ :=
    @inner_eq_top_of_equiv (CFSG.generalizedFitting X) Blueprint.NativeSporadic.Th _
      Units.instGroup ψ inner_Th
  have htop : CFSG.generalizedFitting X = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hα : MulAut.conjNormal x ∈ inner (CFSG.generalizedFitting X) := by
      rw [hinner]
      exact mem_top _
    obtain ⟨f, hf⟩ := hα
    have hcent : (f : X)⁻¹ * x ∈ centralizer (CFSG.generalizedFitting X : Set X) := by
      rw [mem_centralizer_iff]
      intro h hh
      have e := congrArg (fun β : MulAut (CFSG.generalizedFitting X) => (β ⟨h, hh⟩ : X)) hf
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] at e
      calc h * ((f : X)⁻¹ * x) = (f : X)⁻¹ * (f * h * (f : X)⁻¹) * x := by group
        _ = (f : X)⁻¹ * (x * h * x⁻¹) * x := by rw [e]
        _ = (f : X)⁻¹ * x * h := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact f.2
  refine ⟨htop, fun t ht => ?_⟩
  have e : X ≃* Blueprint.NativeSporadic.Th :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans ψ
  exact (thInv_props_of_equiv e ht).2

theorem sporadicOddCoreFree_Th :
    CFSG.ComponentClassification.CatalogueU.SporadicOddCoreFree .Th :=
  fun _ _ _ hF _ hJ t ht =>
    (ctuc_Th_generalized_Fitting_involution_centralizer_exclusion hF hJ).2 t ht

end CFSG.Sporadic.ThSchreier
