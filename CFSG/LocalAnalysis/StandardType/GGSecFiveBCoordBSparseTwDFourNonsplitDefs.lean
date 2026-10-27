module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs

public section

namespace CFSG.StandardType

section Inputs

@[expose] def GGSecFiveBCoordBSparseTwDFourNonsplitInput : Prop :=
  GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput →
  GGNbrTablePNbrInputNarrow → GGForkA8NotReflInput →
  GGRawInnFieldInput → GGRawInndiagIsoInput → GGResNbrFixCentralizesInput →
  BMaxJoinInput → GGSecFiveBCoordBSparseOn
    (fun n p lab => n = 4 ∧ lab.n ≠ 1 ∧ lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1)

end Inputs

end CFSG.StandardType

end
