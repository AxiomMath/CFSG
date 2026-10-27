module

public import Std.Data.HashSet

public section

namespace Certificates.Data.S1277Bfs

open Std

@[expose] def pushNew (seen : HashSet Nat) (q : List Nat) (y : Nat) : List Nat × HashSet Nat :=
  if seen.contains y then (q, seen) else (y :: q, seen.insert y)

@[expose] def expand (moves : List (Nat → Nat)) (x : Nat) (q : List Nat) (seen : HashSet Nat) :
    List Nat × HashSet Nat :=
  moves.foldl (fun acc f => pushNew acc.2 acc.1 (f x)) (q, seen)

@[expose] def bfsAux (moves : List (Nat → Nat)) : Nat → List Nat → HashSet Nat → HashSet Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, x :: q, seen =>
      let r := expand moves x q seen
      bfsAux moves n r.1 r.2

@[expose] def bfs (moves : List (Nat → Nat)) (init : List Nat) (fuel : Nat) : HashSet Nat :=
  bfsAux moves fuel init (init.foldl (fun s x => s.insert x) ∅)

end Certificates.Data.S1277Bfs

end
