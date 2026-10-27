module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterModel
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterIso
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterDiag
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterGraph
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.CGT.Timmesfeld75.L2Real
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceGlue
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.Foundations
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.WeakClosure81.FiveFive
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Certificate18000
public import Certificates.Certificate4058
public import Certificates.Certificate4058Base
public import Certificates.Certificate4071
public import Certificates.Certificate4082
public import Certificates.Certificate4083
public import Certificates.Certificate4083Base
public import Certificates.Certificate43
public import Certificates.Certificate8032
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem seitzFourUOuterModel_of_graphAniso (hR : SeitzFourUGraphAniso) :
    SeitzFourUOuterModel := by
  intro p f K _ h hp n hn E hE h4 hEI
  by_cases hW : ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) ∧
      ∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (φ : K ≃+* K),
        primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A, φ⟩ = e ∧
        ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W
  · obtain ⟨W, hW0, hWi, hWs⟩ := hW
    exact UOuter.planeGen_of_stable_isotropic h hp hn hE h4 hW0 hWi hWs
  by_cases hED : E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  · exact absurd (UOuter.exists_stable_isotropic_of_le_primeFormD h hp hn hE h4 hED hEI) hW
  by_cases h5 : 5 ≤ n
  · exact absurd (UOuter.exists_stable_isotropic_of_not_le_primeFormD h hp h5 hE h4 hED) hW
  refine hR h hp hn (by omega) E hE h4 hED fun W hWi hWs => ?_
  by_contra hW0
  exact hW ⟨W, hW0, hWi, hWs⟩

theorem seitzFourOuter_psu_of_graphAniso (hR : SeitzFourUGraphAniso) :
    SeitzFourOuter fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f :=
  seitzFourOuter_psu_of_model (seitzFourUOuterModel_of_graphAniso hR)

end CFSG.LocalAnalysis.WeakClosure81
