module

public import Certificates.Data.CFSGNative.Co1.Odd
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Co1.S365UNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] def onePlus (Mt : Array Nat) (p : Nat) : Nat := p ^^^ vecMulN 24 Mt p

@[expose] def reduceBy (basis : List (Nat × Nat)) (u q : Nat) : Nat × Nat :=
  basis.foldl (fun acc b => if acc.1.testBit b.1.log2 then (acc.1 ^^^ b.1, acc.2 ^^^ b.2) else acc)
    (u, q)

@[expose] def insertBasis (basis : List (Nat × Nat)) (u q : Nat) : List (Nat × Nat) :=
  let r := reduceBy basis u q
  if r.1 == 0 then basis
  else
    let hi := basis.filter fun b => r.1.log2 < b.1.log2
    let lo := basis.filter fun b => !decide (r.1.log2 < b.1.log2)
    hi ++ (r :: lo)

@[expose] def imBasis (Mt : Array Nat) : List (Nat × Nat) :=
  (List.range 24).foldl (fun basis j => insertBasis basis (onePlus Mt (1 <<< j)) (1 <<< j)) []

@[expose] def memPre (basis : List (Nat × Nat)) (u : Nat) : Option Nat :=
  let r := reduceBy basis u 0
  if r.1 == 0 then some r.2 else none

@[expose] def witness (Qt pts : Array Nat) (pos : Array UInt32) (n : Nat) (Rt St Tt : Array Nat) :
    Option (Nat × Nat × Nat × Nat) :=
  let bR := imBasis Rt
  let bS := imBasis St
  let bT := imBasis Tt
  (List.range (2 ^ bR.length - 1)).findSome? fun m =>
    let mask := m + 1
    let w := (List.range bR.length).foldl
      (fun acc i => if mask.testBit i then (acc.1 ^^^ bR[i]!.1, acc.2 ^^^ bR[i]!.2) else acc)
      (0, 0)
    if type4N Qt pts pos n w.1 then
      match memPre bS w.1, memPre bT w.1 with
      | some p2, some p3 => some (w.1, w.2, p2, p3)
      | _, _ => none
    else none

@[expose] def verifyWit (Qt pts : Array Nat) (pos : Array UInt32) (n : Nat) (Rt St Tt : Array Nat)
    (v p1 p2 p3 : Nat) : Bool :=
  decide (v < 2 ^ 24) && decide (p1 < 2 ^ 24) && decide (p2 < 2 ^ 24) && decide (p3 < 2 ^ 24) &&
    (onePlus Rt p1 == v) && (onePlus St p2 == v) && (onePlus Tt p3 == v) &&
    type4N Qt pts pos n v

@[expose] def uPair (Qt pts : Array Nat) (pos : Array UInt32) (n : Nat) (R S : Array Nat) : Bool :=
  match witness Qt pts pos n (transposeRows 24 R) (transposeRows 24 S)
      (transposeRows 24 (mulRows 24 R S)) with
  | none => false
  | some (v, p1, p2, p3) =>
    verifyWit Qt pts pos n (transposeRows 24 R) (transposeRows 24 S)
      (transposeRows 24 (mulRows 24 R S)) v p1 p2 p3

@[expose] def uScan (Qt pts : Array Nat) (pos : Array UInt32) (n : Nat) (R : Array Nat)
    (Pts : Array (Array Nat)) : Bool :=
  let set : Std.HashSet (Array Nat) := Std.HashSet.ofList Pts.toList
  Pts.all fun S =>
    !(mulRows 24 R S == mulRows 24 S R && set.contains (mulRows 24 R S)) ||
      uPair Qt pts pos n R S

end CFSG.Sporadic.Co1.S365UNative
