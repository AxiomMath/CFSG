module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.Code.Basis
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import CFSG.Monster.Code.Basis
import Mathlib.Data.Nat.Bitwise
public meta import CFSG.Monster.Code.Weights
public meta import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot

@[expose] def combI (m : ℕ) : ℕ :=
  (List.range 12).foldl (fun acc k => if m.testBit k then acc ^^^ Bmask k else acc) 0

@[expose] def validList : List ℕ := ((List.range 4096).map combI).filter (· < 2 ^ 23)

end CFSG.Monster.B.TwoA.Census
