module

public import CFSG.Quasithin.EmptyFaithful.SBd8Top
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagL4
public import CFSG.Quasithin.EmptyFaithful.SBd8L5
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
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
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.SBd8Small
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

theorem famL4_holds : FamL4 := fun _ _ _ _ _ _ d ⟨e⟩ => famL4 d e

theorem famL5_holds : FamL5 := fun _ _ _ _ _ _ d ⟨e⟩ => famL5 d e

theorem input28Insp_holds (hG2 : FactG2Cayley) : Input28Insp :=
  input28Insp_of_flags hG2 famL4_holds famL5_holds

end SBd8

end CFSG.Quasithin
