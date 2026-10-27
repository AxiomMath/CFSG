module

public import Std.Data.HashSet

public section

namespace Certificates.Data.S1277Sig

open Std

@[expose] def applyCols : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, x => (if x % 2 = 1 then c else 0) ^^^ applyCols cs (x / 2)

@[expose] def compCols (a b : List Nat) : List Nat := b.map (applyCols a)

@[expose] def idCols (d : Nat) : List Nat := (List.range d).map fun i => 2 ^ i

@[expose] def okPre (φ : Nat → Nat) (cols : List Nat) : Bool :=
  (List.range (2 ^ cols.length)).all fun x => φ (applyCols cols x) == φ x

@[expose] def okInc (φ : Nat → Nat) (p : List Nat) (c : Nat) : Bool :=
  (List.range (2 ^ p.length)).all fun y => φ (c ^^^ applyCols p y) == φ (2 ^ p.length + y)

@[expose] def sigEnum (d : Nat) (φ : Nat → Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 =>
    (sigEnum d φ k).flatMap fun p =>
      ((List.range (2 ^ d)).filter fun c => okInc φ p c).map fun c => p ++ [c]

@[expose] def injCols (d : Nat) (cols : List Nat) : Bool :=
  decide (((List.range (2 ^ d)).map (applyCols cols)).Nodup)

@[expose] def sigList (d : Nat) (φ : Nat → Nat) : List (List Nat) :=
  (sigEnum d φ d).filter (injCols d)

end Certificates.Data.S1277Sig

end
