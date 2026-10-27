
module

public import CFSG.Monster.B.TwoA.Unitary.OrbitBase
public import CFSG.Monster.B.TwoA.Base.FrameBase
public import CFSG.Monster.B.Classical.ThreePlaneData
public meta import CFSG.Monster.B.TwoA.Census.PermCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.Code.Weights

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] restAction

@[expose] def permGens : Array (Array ℕ) := n6PermArr

@[expose] def p2Cert : TreeCert := bfsCert amul permGens idArr 41000

end CFSG.Monster.B.TwoA.Unitary
