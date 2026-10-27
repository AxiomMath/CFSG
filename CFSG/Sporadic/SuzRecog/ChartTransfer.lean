module

public import CFSG.Sporadic.SuzRecog.ChartTransferCore
public import CFSG.Sporadic.SuzRecog.GluingProof
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Monster.Code.Weights
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.Sporadic.SuzRecog.ChartGluing
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension

public section

namespace CFSG.Sporadic.SuzRecog

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.Sporadic.SuzOddCore

theorem suzChartTransfer_conj
    {c : Equiv.Perm (Fin 1782)}
    (hc : c ∈ invE 1) : SuzChartTransfer (c * qVec 1 * c⁻¹) :=
  fun _ _ _ _ S hS σ => RigidL2.chartTransfer_conj S hS.1 hS.2.2.1 hS.2.2.2.1 σ hc

end CFSG.Sporadic.SuzRecog
