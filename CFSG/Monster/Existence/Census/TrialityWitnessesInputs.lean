module

public import CFSG.Monster.B.TwoA.Census.SymTrace
public import CFSG.Monster.Existence.Census.RigidInputs
public import CFSG.Monster.Generated.Data

public section

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def idArr : Array ℕ :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]

end CFSG.Monster.Existence.Census
