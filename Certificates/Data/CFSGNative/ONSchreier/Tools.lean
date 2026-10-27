module

public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Std.Data.HashMap

public section

namespace CFSG.ONSchreier.Native

set_option compiler.extract_closed false

@[expose] def posArr (n : Nat) (R : Array Nat) : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate n R.size
  for k in [0:R.size] do
    t := t.set! R[k]! k
  return t

@[expose] def restrictTab (g R rpos : Array Nat) : Array Nat := R.map fun p => rpos[g[p]!]!

@[expose] def pointsOK (n : Nat) (R rpos : Array Nat) : Bool :=
  rpos.size == n && allBelowN R.size fun k => decide (R[k]! < n) && rpos[R[k]!]! == k

@[expose] def blockPos (n : Nat) (B : Array (Array Nat)) : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate n B.size
  for i in [0:B.size] do
    for p in B[i]! do
      t := t.set! p i
  return t

@[expose] def blocksOK (n : Nat) (B : Array (Array Nat)) (bpos : Array Nat) : Bool :=
  bpos.size == n && allBelowN B.size fun i => B[i]!.size == 2 && decide (B[i]![0]! < n) &&
    decide (B[i]![1]! < n) && B[i]![0]! != B[i]![1]! && bpos[B[i]![0]!]! == i &&
    bpos[B[i]![1]!]! == i

@[expose] def blockTab (g : Array Nat) (B : Array (Array Nat)) (bpos : Array Nat) : Array Nat :=
  B.map fun b => bpos[g[b[0]!]!]!

@[expose] def blocksMapOK (g : Array Nat) (B : Array (Array Nat)) (bpos : Array Nat) : Bool :=
  allBelowN B.size fun i => decide (bpos[g[B[i]![0]!]!]! < B.size) &&
    bpos[g[B[i]![1]!]!]! == bpos[g[B[i]![0]!]!]!

@[expose] def dedupTabs (n : Nat) (ts : List (Array Nat)) : List (Array Nat) :=
  ts.foldl (fun acc t => if peq n t (pid n) || acc.any (fun u => peq n u t) then acc
    else acc ++ [t]) []

@[expose] def fixCount (n : Nat) (g : Array Nat) : Nat :=
  ((List.range n).filter fun i => g[i]! == i).length

@[expose] def fixedSet (n : Nat) (gens : Array (Array Nat)) : List Nat :=
  (List.range n).filter fun i => gens.all fun g => g[i]! == i

@[expose] def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

@[expose] def sortedImage (g : Array Nat) (b : Array Nat) : List Nat :=
  b.toList.foldl (fun acc p => insertSorted g[p]! acc) []

@[expose] def setTab (g : Array Nat) (B : Array (Array Nat)) : Array Nat :=
  let index : Std.HashMap (List Nat) Nat :=
    (List.range B.size).foldl (fun m i => m.insert B[i]!.toList i) ∅
  B.map fun b => index.getD (sortedImage g b) B.size

end CFSG.ONSchreier.Native
