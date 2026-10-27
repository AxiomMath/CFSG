module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Rank

open CFSG.Sporadic.SmallF2.Native

@[expose] def commRows (X Y : Array Nat) : Bool := mulRows 22 X Y == mulRows 22 Y X

@[expose] def posMap (V : Array (Array Nat)) : Std.HashMap (Array Nat) Nat :=
  (List.range V.size).foldl (fun m k => m.insert V[k]! k) ∅

@[expose] def prF (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) (i j : Nat) : Nat :=
  pos.getD (mulRows 22 V[i]! V[j]!) V.size

@[expose] def adjF (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) (i j : Nat) : Bool :=
  commRows V[i]! V[j]! && decide (prF V pos i j < V.size) && V[prF V pos i j]! == mulRows 22 V[i]! V[j]!

@[expose] def buildAdj (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) : ByteArray :=
  Id.run do
    let mut t : ByteArray := ByteArray.empty
    for i in [0:V.size] do
      for j in [0:V.size] do
        t := t.push (if adjF V pos i j then 1 else 0)
    return t

@[expose] def buildPr (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) : ByteArray :=
  Id.run do
    let mut t : ByteArray := ByteArray.empty
    for i in [0:V.size] do
      for j in [0:V.size] do
        if adjF V pos i j then
          let p := prF V pos i j
          t := (t.push (p % 256).toUInt8).push (p / 256).toUInt8
        else
          t := (t.push 0).push 0
    return t

@[expose] def adjL (n : Nat) (t : ByteArray) (i j : Nat) : Bool :=
  decide (i < n) && decide (j < n) && t.get! (i * n + j) != 0

@[expose] def prL (n : Nat) (t : ByteArray) (i j : Nat) : Nat :=
  (t.get! (2 * (i * n + j))).toNat + 256 * (t.get! (2 * (i * n + j) + 1)).toNat

@[expose] def tablesOK (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat)
    (adjT prT : ByteArray) : Bool :=
  adjT.size == V.size * V.size && prT.size == 2 * (V.size * V.size) &&
    (List.range V.size).all fun i => (List.range V.size).all fun j =>
      (adjL V.size adjT i j == adjF V pos i j) &&
        (!adjL V.size adjT i j || prL V.size prT i j == prF V pos i j)

@[expose] def kids (pr : Nat → Nat → Nat) (S cand : List Nat) (lo : Nat) : List Nat :=
  cand.filter fun c => decide (lo ≤ c) && S.all fun s => decide (c < pr c s)

@[expose] def childS (pr : Nat → Nat → Nat) (S : List Nat) (c : Nat) : List Nat :=
  c :: (S ++ S.map (pr c))

@[expose] def childCand (adj : Nat → Nat → Bool) (pr : Nat → Nat → Nat) (S cand : List Nat)
    (c : Nat) : List Nat :=
  cand.filter fun d => adj c d && S.all fun s => adj (pr c s) d

@[expose] def dfs (adj : Nat → Nat → Bool) (pr : Nat → Nat → Nat) :
    Nat → List Nat → List Nat → Nat → Bool
  | 0, S, cand, lo => (kids pr S cand lo).isEmpty
  | d + 1, S, cand, lo => (kids pr S cand lo).all fun c =>
      dfs adj pr d (childS pr S c) (childCand adj pr S cand c) (c + 1)

end CFSG.Sporadic.Co2Rank
