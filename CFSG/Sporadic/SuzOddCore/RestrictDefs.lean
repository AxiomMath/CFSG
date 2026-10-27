module


public section

namespace CFSG.Sporadic.SuzOddCore

@[expose] def restrictArr (L : List Nat) (t : Array Nat) : Array Nat :=
  (L.map fun x => L.idxOf t[x]!).toArray

@[expose] def fixedList (n : Nat) (t : Array Nat) : List Nat :=
  (List.range n).filter fun x => t[x]! == x

@[expose] def fixedCountN (n : Nat) (t : Array Nat) : Nat := (fixedList n t).length

end CFSG.Sporadic.SuzOddCore
