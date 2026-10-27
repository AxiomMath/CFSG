module

public import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import Mathlib.Init
public import Mathlib.Init

public section

namespace CFSG.Sporadic.ONOddCore

@[expose] def candLift : Cand → Option Nat
  | .lift i => some i
  | .rel _ _ => none

@[expose] def liftIdxs (cs : List Cand) : List Nat := cs.filterMap candLift

end CFSG.Sporadic.ONOddCore
