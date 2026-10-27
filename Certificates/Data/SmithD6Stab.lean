module

public import Certificates.Data.SmithD6Check

public noncomputable section

namespace CFSG.SmithD6

@[expose] def lineMeet (a : Nat) : Nat :=
  let p0 := linePair 0
  let p := linePair a
  ([p0.1, p0.2, p0.1 ^^^ p0.2].filter fun x => [p.1, p.2, p.1 ^^^ p.2].contains x).length

@[expose] def lineRank (a : Nat) : Nat :=
  let p0 := linePair 0
  let p := linePair a
  let r0 := (bf p0.1 p.1).toNat + 2 * (bf p0.1 p.2).toNat
  let r1 := (bf p0.2 p.1).toNat + 2 * (bf p0.2 p.2).toNat
  if r0 == 0 && r1 == 0 then 0 else if r0 == 0 || r1 == 0 || r0 == r1 then 1 else 2

@[expose] def stabCls (a : Nat) : Nat :=
  if a == 0 then 0
  else if lineMeet a == 1 then (if lineRank a == 0 then 1 else 2)
  else if lineRank a == 0 then 3 else if lineRank a == 1 then 4 else 5

@[expose] def stabSizes : Array Nat := #[1, 810, 768, 25200, 207360, 131072]

@[expose] def stabOrd : Array Nat := #[1, 2, 2, 2, 4, 3]

def rootLines : Array Nat :=
  ((List.range 6).flatMap fun i => (List.range 6).flatMap fun j =>
    if i < j then [lineOf (eV i) (eV j), lineOf (fV i) (fV j), lineOf (eV i) (fV j),
      lineOf (fV i) (eV j)] else []).toArray

def stabGens : Array Nat := rootLines.filter fun g => g != 0 && tvImg g 0 == 0

def stabReps : Array Nat :=
  (Array.range 6).map fun c => ((List.range 365211).find? fun a => stabCls a == c).getD 0

@[expose] def stabRep (c : Nat) : Nat := stabReps[c]!

def stabTree : Array Nat × Array Nat × Array Nat :=
  treeBFS 365211 (Array.range stabGens.size) (fun g v => tvImg stabGens[g]! v) stabReps.toList

@[expose] def chkStabTree : Bool :=
  stabReps.size == 6 &&
  (List.range 6).all (fun c => decide (stabRep c < 365211) && stabCls (stabRep c) == c) &&
  stabGens.all (fun g => decide (g < 365211) && tvImg g 0 == 0) &&
  treeOK 365211 stabGens.size (fun v => v == stabRep (stabCls v))
    (fun g p v => stabCls p == stabCls v && tvImg stabGens[g]! p == v) stabTree

@[expose] def chkStabCard : Bool :=
  (List.range 6).all fun c => ((List.range 365211).filter fun a => stabCls a == c).length ==
    stabSizes[c]!

@[expose] def chkStabNc : Bool :=
  stabGens.size == 42 && tvImg stabGens[0]! stabGens[1]! != stabGens[1]!

@[expose] def prodStep (a b x : Nat) : Nat :=
  sgl (linePair a).1 (linePair a).2 (sgl (linePair b).1 (linePair b).2 x)

@[expose] def prodPow (a b : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => prodPow a b n (prodStep a b x)

@[expose] def chkStabOrd : Bool :=
  stabOrd.size == 6 && (List.range 6).all (fun c =>
    let r := stabRep c
    (List.range 4096).all (fun x => prodPow 0 r stabOrd[c]! x == x) &&
    (if stabOrd[c]! == 1 then true
     else if stabOrd[c]! == 4 then (List.range 4096).any fun x => prodPow 0 r 2 x != x
     else (List.range 4096).any fun x => prodStep 0 r x != x)) &&
  linePair 31899 == (fV 0, fV 1) && stabCls 31899 == 5

end CFSG.SmithD6
