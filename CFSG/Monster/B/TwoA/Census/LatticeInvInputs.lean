module

public import CFSG.Monster.B.TwoA.Census.XiFusion
public import CFSG.Monster.VisCert.FrameOrbit
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.Monster.B.TwoA.Census.SymTrace
public meta import CFSG.Monster.B.TwoA.Census.XiFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  Matrix

@[expose] def chiF (g : Matrix (Fin 24) (Fin 24) ℚ) : ℚ := ((trace g) ^ 2 + trace (g * g)) / 2 - 1

end CFSG.Monster.B.TwoA.Census
