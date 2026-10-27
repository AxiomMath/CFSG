module

public import CFSG.Sporadic.Co2InvData
public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.OrderCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.Co2InvData
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public meta import CFSG.Sporadic.Co2Cert.OrderCheck
public meta import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Inv

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

@[expose] def sOrder : Nat := 262144

structure SEnum where
  elems : Array (Array Nat)
  par : Array Nat
  lab : Array Nat
  tbl : Array (Array Nat)
  pos : Std.HashMap (Array Nat) Nat

@[expose] def bfsS (gens : Array (Array Nat)) (cap : Nat) : SEnum := Id.run do
  let mut elems : Array (Array Nat) := #[idRows 22]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut tbl : Array (Array Nat) := #[]
  let mut pos : Std.HashMap (Array Nat) Nat :=
    (∅ : Std.HashMap (Array Nat) Nat).insert (idRows 22) 0
  for h in [0:cap] do
    if h < elems.size then
      let x := elems[h]!
      let mut row : Array Nat := #[]
      for j in [0:gens.size] do
        let y := mulRows 22 x gens[j]!
        match pos.get? y with
        | some i => row := row.push i
        | none =>
          pos := pos.insert y elems.size
          row := row.push elems.size
          elems := elems.push y
          par := par.push h
          lab := lab.push j
      tbl := tbl.push row
  return ⟨elems, par, lab, tbl, pos⟩

@[expose] def enumS : SEnum := bfsS co2InvGens sOrder

@[expose] def wfRows (A : Array Nat) : Bool := A.size == 22 && A.all (· < 2 ^ 22)

@[expose] def isInvolRows (X : Array Nat) : Bool :=
  mulRows 22 X X == idRows 22 && X != idRows 22

@[expose] def firstIdPow (Q : Array Nat) : Nat → Array Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, P, e => if P == idRows 22 then some e else firstIdPow Q fuel (mulRows 22 P Q) (e + 1)

@[expose] def oddPowOK (Q : Array Nat) : Bool :=
  match firstIdPow Q 64 (powRows 22 Q 1) 1 with
  | some e => e % 2 == 1
  | none => false

@[expose] def seedRows (l : Nat) : Array Nat := if l = 0 then co2RowsA else co2RowsB

@[expose] def wordRowsSeed : List Nat → Array Nat
  | [] => idRows 22
  | l :: w => mulRows 22 (seedRows l) (wordRowsSeed w)

@[expose] def candW (c : Nat) : Array Nat := wordRowsSeed (co2InvCands[c]!).2

@[expose] def candY (c : Nat) : Array Nat :=
  mulRows 22 (mulRows 22 (candW c) co2InvReps[(co2InvCands[c]!).1]!)
    (CFSG.Monster.B.Max2.Native.inv22 (candW c))

@[expose] def candYs : Array (Array Nat) := Array.ofFn (n := 54) fun c => candY c

@[expose] def fuseOK (Y : Array (Array Nat)) (X : Array Nat) : Bool :=
  (List.range Y.size).any fun c => oddPowOK (mulRows 22 X Y[c]!)

@[expose] def enumCheck (E : SEnum) (Y : Array (Array Nat)) : Bool :=
  E.elems.size == sOrder && E.elems[0]! == idRows 22 &&
    allLt sOrder (fun k => wfRows E.elems[k]!) &&
    allLt sOrder (fun k => k == 0 || (decide (E.par[k]! < k) && decide (E.lab[k]! < 5) &&
      E.elems[k]! == mulRows 22 E.elems[E.par[k]!]! co2InvGens[E.lab[k]!]!)) &&
    allLt sOrder (fun k => allLt 5 fun j => decide ((E.tbl[k]!)[j]! < sOrder) &&
      E.elems[(E.tbl[k]!)[j]!]! == mulRows 22 E.elems[k]! co2InvGens[j]!) &&
    allLt sOrder (fun k => E.pos.getD E.elems[k]! 0 == k) &&
    allLt sOrder (fun k => !(isInvolRows E.elems[k]!) || fuseOK Y E.elems[k]!) &&
    allLt 3 (fun r => decide (E.pos.getD co2InvReps[r]! 0 < sOrder) &&
      E.elems[E.pos.getD co2InvReps[r]! 0]! == co2InvReps[r]!)

@[expose] def genPermWith (pt : Array UInt32) (j : Nat) : Array Nat :=
  let gt := transposeRows 22 co2InvGens[j]!
  Array.ofFn (n := 2300) fun i => (pt[vecMulN 22 gt co2PackedVecs[i.val]!]!).toNat

@[expose] def genCheckOne (levels : Array Level) (pt : Array UInt32) (j : Nat) : Bool :=
  let gt := transposeRows 22 co2InvGens[j]!
  let p := genPermWith pt j
  wfRows co2InvGens[j]! && p.size == 2300 && isInvA 2300 p (invCand 2300 p) &&
    allLt 2300 (fun i => co2PackedVecs[p[i]!]! == vecMulN 22 gt co2PackedVecs[i]!) &&
    siftA 2300 levels co2BaseArr 0 p

@[expose] def gensCheck (levels : Array Level) (pt : Array UInt32) : Bool :=
  co2InvGens.size == 5 && allLt 5 fun j => genCheckOne levels pt j

@[expose] def candCheck : Bool :=
  co2InvCands.size == 54 && allLt 54 fun c =>
    decide ((co2InvCands[c]!).1 < 3) &&
      mulRows 22 (candW c) (CFSG.Monster.B.Max2.Native.inv22 (candW c)) == idRows 22

@[expose] def addId (X : Array Nat) : Array Nat :=
  Array.ofFn (n := 22) fun i => X[i.val]! ^^^ (1 <<< i.val)

@[expose] def truncId (r : Nat) : Array Nat :=
  Array.ofFn (n := 22) fun i => if i.val < r then 1 <<< i.val else 0

@[expose] def rankCheck : Bool :=
  co2InvReps.size == 3 && allLt 3 fun r =>
    wfRows co2InvReps[r]! && isInvolRows co2InvReps[r]! &&
      mulRows 22 co2InvRankP[r]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankP[r]!) ==
        idRows 22 &&
      mulRows 22 co2InvRankQ[r]! (CFSG.Monster.B.Max2.Native.inv22 co2InvRankQ[r]!) ==
        idRows 22 &&
      mulRows 22 (mulRows 22 co2InvRankP[r]! (addId co2InvReps[r]!)) co2InvRankQ[r]! ==
        truncId (6 + 2 * r)

end CFSG.Sporadic.Co2Inv
