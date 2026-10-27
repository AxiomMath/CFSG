module

public import Init

public section

namespace CFSG.KC.F2Rows

@[expose] def ofBitsF (n : Nat) (g : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc j => if g j then acc ||| (1 <<< j) else acc) 0

@[expose] def xorRow (n : Nat) (Y : List Nat) (x : Nat) : Nat :=
  (List.range n).foldl (fun acc t => if x.testBit t then acc ^^^ Y.getD t 0 else acc) 0

@[expose] def mulR (n : Nat) (X Y : List Nat) : List Nat := X.map (xorRow n Y)

@[expose] def addR (m : Nat) (X Y : List Nat) : List Nat :=
  (List.range m).map fun i => X.getD i 0 ^^^ Y.getD i 0

@[expose] def idR (m : Nat) : List Nat := (List.range m).map fun i => 1 <<< i

end CFSG.KC.F2Rows
