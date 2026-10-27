module

public import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native

@[expose] def ruMixA (p : ℕ) : Array ℕ :=
  compA 4060 (ruYpA p) (compA 4060 (compA 4060 ruLGensA[0]! (ruYpA p)) (ruInv ruLGensA[0]!))

end CFSG.Sporadic.RuSchreier
