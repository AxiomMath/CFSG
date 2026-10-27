module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOffQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpFourCommonDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabelOfJDefs
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Leaves


@[expose] def GGSecFiveBCoordBOffQTwoOrthRouteInput : Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → GGStdSubPrimeInput → GGResXDichotomyInput →
    GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput →
    GGRawInnFieldInput → GGRawInndiagIsoInput → GGResNbrFixCentralizesInput → BMaxJoinInput →
    GGSecFivePermNbrLabelOfJInput → GGU62OuterDiagInput →
      (GGSecFiveBCoordBOffSpOn fun _ _ lab => lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))

@[expose] def GGSecFiveBCoordBSpFourCommonChartRouteInput : Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → GGStdSubPrimeInput → GGResXDichotomyInput →
    GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput →
    GGRawInnFieldInput → GGRawInndiagIsoInput → GGResNbrFixCentralizesInput → BMaxJoinInput →
      GGSecFiveBCoordBSpFourCommonChartInput

@[expose] def GGSecFiveBCoordBSpFourCommonCompRouteInput : Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → GGStdSubPrimeInput → GGResXDichotomyInput →
    GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput →
    GGRawInnFieldInput → GGRawInndiagIsoInput → GGResNbrFixCentralizesInput → BMaxJoinInput →
      GGSecFiveBCoordBSpFourCommonCompInput

@[expose] def GGSecFiveBCoordBSparseTwDFiveNonsplitInput : Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → GGStdSubPrimeInput → GGResXDichotomyInput →
    GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput →
    GGRawInnFieldInput → GGRawInndiagIsoInput → GGResNbrFixCentralizesInput → BMaxJoinInput →
      GGSecFiveBCoordBSparseOn fun n p lab =>
        5 ≤ n ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1

end Leaves

end CFSG.StandardType

end
