module

public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMinus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTables
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
import CFSG.Foundations
import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldFamily
import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphRange
import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamFinal
import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSpinCover
import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowRange
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmega
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTQuotRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeFieldFour
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.Sporadic.Bridge.LyData
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.HN.CertificateBase
import CFSG.Sporadic.Ly.ActionBase
import CFSG.Sporadic.Ly.CertificateBase
import CFSG.Sporadic.Ly.FaithSpec
import CFSG.Sporadic.Ly.OrbitSpec
import CFSG.Sporadic.Ly.Simple
import CFSG.Sporadic.LyBase
import CFSG.Sporadic.ON.SimpleBase
import CFSG.Sporadic.Presentation.Ly
import CFSG.Sporadic.Schreier.LyChain11
import Certificates.Certificate1016Base
import Certificates.Certificate1021
import Certificates.Certificate3085Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pow_three_dvd_card_statedOmega_quadPlus_three :
    Nat.card K ^ 3 ∣ Nat.card ↥(StatedOmega (StatedQuadPlus 3 K)) := by
  rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadPlus_three_any,
    CFSG.SeitzReduction.F4Pilot.ordSL_four (Nat.card K)]
  exact Dvd.dvd.mul_right (pow_dvd_pow (Nat.card K) (by norm_num : 3 ≤ 6)) _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
