module

public import CFSG.RankThree.PartOne.SEITZ12.Consumer
public import CFSG.RankThree.PartOne.SEITZ12.Final
public import CFSG.RankThree.PartOne.D4RC.Phi6
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.RankThree.PartOne.CTP.StdSub
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.SEITZ11.G2SevenAPI
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate8153
public import Certificates.Certificate8156
public import Certificates.Certificate8157
public import Certificates.Certificate8160
public import Certificates.Certificate8171
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.RankThree.PartOne.SEITZ12

set_option linter.unusedSectionVars false


theorem exc2F4NonsplitPhi4_holds : CFSG.RankThree.PartOne.SEITZ2.Exc2F4NonsplitPhi4 := by
  refine exc2F4NonsplitPhi4_of_ambient ?_
  intro m K _ _ _ hm hK
  exact phi4_ambient_holds hm hK

section Ledger


theorem seitzResidualFinePairOdd_of_three (h : SEITZ2.SeitzFieldAutFineOdd ∧ D4RC.Max3D4CentN6 ∧
    SEITZ2.Exc2F4NonsplitPhi2) :
    SEITZ2.SeitzResidualFinePairOdd :=
  ⟨h.1, D4RC.exc3D4NonsplitPhi3Phi6_of_phi6 h.2.1, exc2F4NonsplitPhi4_holds, h.2.2⟩

theorem seitzResidualFinePairOdd_of_two (h : SEITZ2.SeitzFieldAutFineOdd ∧
    SEITZ2.Exc2F4NonsplitPhi2) :
    SEITZ2.SeitzResidualFinePairOdd :=
  seitzResidualFinePairOdd_of_three ⟨h.1, D4RC.rc6_max3D4CentN6, h.2⟩

end Ledger

end CFSG.RankThree.PartOne.SEITZ12
