module

public import Certificates.Data.CFSGNative.Bridge.SurjA
public import Certificates.Data.CFSGNative.J3.Data

public section

namespace J3E27

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native

set_option compiler.extract_closed false

@[expose] def zLetter (z : Int) : Nat × Bool := (if z.natAbs = 1 then 0 else 1, decide (0 < z))

@[expose] def zWord (l : List Int) : List (Nat × Bool) := l.map zLetter

@[expose] def invW (w : List (Nat × Bool)) : List (Nat × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def wordW1 : List (Nat × Bool) := zWord
  [2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
    2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1,
    -2, 1, -2, 1]

@[expose] def wordX3 : List (Nat × Bool) := zWord
  [-2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
    -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1,
    -2, 1, 2, 1, 2, 1, -2]

@[expose] def wordS : List (Nat × Bool) := zWord
  [1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
    2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1,
    2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2]

@[expose] def wordT : List (Nat × Bool) := zWord
  [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1,
    2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1,
    -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1]

@[expose] def wordW2 : List (Nat × Bool) := wordS ++ wordW1 ++ invW wordS

end J3E27
