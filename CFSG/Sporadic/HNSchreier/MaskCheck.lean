module

public import Init

public section

namespace CFSG.Sporadic.HNSchreier.Native

@[expose] def maskOfList (l : List Nat) : Nat := l.foldl (fun m s => m ||| (1 <<< s)) 0

@[expose] def permMask (p : Array Nat) (m : Nat) : Nat :=
  (List.range 12).foldl (fun acc i => if m.testBit i then acc ||| (1 <<< p[i]!) else acc) 0

@[expose] def canonMask (m : Nat) : Nat := if m.testBit 0 then m else 4095 ^^^ m

@[expose] def popc12 (m : Nat) : Nat := Nat.fold 12 (fun i _ acc => if m.testBit i then acc + 1
  else acc) 0

end CFSG.Sporadic.HNSchreier.Native
