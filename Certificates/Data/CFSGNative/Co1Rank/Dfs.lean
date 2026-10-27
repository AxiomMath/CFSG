module

public import Certificates.Data.CFSGNative.Co1.TwoB
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Std.Data.HashSet
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co1.RankNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative

@[expose] def xFixCnt (V : Array Nat) (r : Array Nat) : Nat :=
  let Mt := transposeRows 24 r
  countBelow (fun i => vecMulN 24 Mt V[i]! == V[i]!) 98280 0

@[expose] def isNonA (V : Array Nat) (r : Array Nat) : Bool :=
  mulRows 24 r r == idRows 24 && r != idRows 24 && xFixCnt V r != 2280

@[expose] def nonAList (V : Array Nat) (pts : Array (Array Nat)) : List (Array Nat) :=
  pts.toList.filter (isNonA V)

@[expose] def univOf (c : Array Nat) (R1 : List (Array Nat)) : Array (Array Nat) :=
  let S1 : Std.HashSet (Array Nat) := Std.HashSet.ofList R1
  (c :: R1.filter fun y =>
    y != c && mulRows 24 c y == mulRows 24 y c && S1.contains (mulRows 24 c y)).toArray

@[expose] def idxMap (U : Array (Array Nat)) : Std.HashMap (Array Nat) Nat :=
  Std.HashMap.ofList U.toList.zipIdx

@[expose] def lookupIdx (U : Array (Array Nat)) (m : Std.HashMap (Array Nat) Nat)
    (p : Array Nat) : Int :=
  match m[p]? with
  | some c => if c < U.size && U[c]! == p then (c : Int) else -1
  | none => -1

@[expose] def tabEntry (U : Array (Array Nat)) (m : Std.HashMap (Array Nat) Nat) (a b : Nat) :
    Int :=
  if a < b then
    if mulRows 24 U[a]! U[b]! == mulRows 24 U[b]! U[a]! then
      lookupIdx U m (mulRows 24 U[a]! U[b]!)
    else -1
  else -1

@[expose] def tabOf (U : Array (Array Nat)) (m : Std.HashMap (Array Nat) Nat) :
    Array (Array Int) :=
  (Array.range U.size).map fun a => (Array.range U.size).map fun b => tabEntry U m a b

@[expose] def tab (T : Array (Array Int)) (a b : Nat) : Int :=
  if a < b then T[a]![b]! else T[b]![a]!

@[expose] def dfs (T : Array (Array Int)) (target : Nat) : Nat → List Nat → List Nat → Bool
  | 0, sub, _ => decide (sub.length + 1 < target)
  | fuel + 1, sub, cand =>
    if target ≤ sub.length + 1 then false
    else if sub.length + 1 + cand.length < target then true
    else cand.all fun x =>
      let sub2 := x :: (sub ++ sub.map fun s => (tab T x s).toNat)
      dfs T target fuel sub2 (cand.filter fun y => decide (x < y) &&
        sub2.all fun t => decide (0 ≤ tab T y t) && decide (x < (tab T y t).toNat))

@[noinline, expose] def rankCheckOf (gens : Array (Array Nat)) (cap : Nat) (V : Array Nat)
    (c : Array Nat) : Bool :=
  let T := gtBFS gens cap
  let U := univOf c (nonAList V T.pts)
  let m := idxMap U
  let tb := tabOf U m
  gtOK gens T && T.pts.size == cap &&
    gens.all (fun g => mulRows 24 g c == mulRows 24 c g) && validRows c && isNonA V c &&
    (List.range U.size).all (fun j => lookupIdx U m U[j]! == (j : Int)) &&
    dfs tb 64 U.size [0] ((List.range U.size).filter fun y => decide (0 < y) && decide (0 ≤ tab tb 0 y))

end CFSG.Sporadic.Co1.RankNative
