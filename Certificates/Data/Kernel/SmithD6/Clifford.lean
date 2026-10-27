module

public section

namespace CFSG.SmithD6

@[expose] def xorFold (n : Nat) (f : Nat → Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc ^^^ f i) 0

@[expose] def inMask (i : Nat) : Nat :=
  match i with
  | 0 => 0xAAAAAAAAAAAAAAAA
  | 1 => 0xCCCCCCCCCCCCCCCC
  | 2 => 0xF0F0F0F0F0F0F0F0
  | 3 => 0xFF00FF00FF00FF00
  | 4 => 0xFFFF0000FFFF0000
  | _ => 0xFFFFFFFF00000000

@[expose] def outMask (i : Nat) : Nat := 0xFFFFFFFFFFFFFFFF ^^^ inMask i

@[expose] def wedC (i s : Nat) : Nat := (s &&& outMask i) <<< 2 ^ i

@[expose] def contrC (i s : Nat) : Nat := (s &&& inMask i) >>> 2 ^ i

@[expose] def rhoC (x s : Nat) : Nat :=
  xorFold 6 (fun i => bif x.testBit i then wedC i s else 0) ^^^
    xorFold 6 (fun i => bif x.testBit (6 + i) then contrC i s else 0)

@[expose] def termC (t : Nat × Nat × Bool) (s : Nat) : Nat :=
  bif t.2.2 then (s &&& t.1) <<< t.2.1 else (s &&& t.1) >>> t.2.1

@[expose] def rhoT (ts : List (Nat × Nat × Bool)) (s : Nat) : Nat :=
  ts.foldr (fun t acc => termC t s ^^^ acc) 0

@[expose] def liftT (ts : List (Nat × Nat × Bool)) (s : Nat) : Nat := s ^^^ rhoT ts s

@[expose] def rhoTOK (u w : Nat) (ts : List (Nat × Nat × Bool)) : Bool :=
  (List.range 64).all fun S => rhoT ts (2 ^ S) == rhoC u (rhoC w (2 ^ S))

end CFSG.SmithD6
