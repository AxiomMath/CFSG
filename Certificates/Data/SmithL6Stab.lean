module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

@[expose] def stabCls (a : Nat) : Nat :=
  if a = 0 then 0 else
  if (tvPair a).1 = (tvPair 0).1 then 1 else
  if (tvPair a).2 = (tvPair 0).2 then 2 else
  3 + 2 * (if form (tvPair 0).2 (tvPair a).1 then 1 else 0) +
    (if form (tvPair a).2 (tvPair 0).1 then 1 else 0)

@[expose] def stabTvGens : Array Nat :=
  (Array.range 1953).filter fun g => g != 0 && tvImg g 0 == 0

@[expose] def stabReps : Array Nat :=
  (Array.range 7).map fun c => ((List.range 1953).find? fun a => stabCls a == c).getD 0

@[expose] def stabRep (c : Nat) : Nat := stabReps[c]!

@[expose] def bfsRound (gens : Array Nat) (T : Array (Nat × Nat × Nat)) (F : Array Nat) :
    Array (Nat × Nat × Nat) × Array Nat :=
  F.foldl (fun acc a =>
    gens.foldl (fun acc g =>
      let b := tvImg g a
      if acc.1[b]!.2.2 == 2000 then (acc.1.set! b (g, a, acc.1[a]!.2.2 + 1), acc.2.push b)
      else acc) acc) (T, #[])

@[expose] def bfsGo (gens : Array Nat) : Nat → Array (Nat × Nat × Nat) → Array Nat →
    Array (Nat × Nat × Nat)
  | 0, T, _ => T
  | fuel + 1, T, F => if F.isEmpty then T else
      let r := bfsRound gens T F
      bfsGo gens fuel r.1 r.2

@[expose] def bfsTree (gens roots : Array Nat) : Array (Nat × Nat × Nat) :=
  bfsGo gens 1953 (roots.foldl (fun T r => T.set! r (0, r, 0)) (Array.replicate 1953 (0, 0, 2000)))
    roots

@[expose] def stabTree : Array (Nat × Nat × Nat) := bfsTree stabTvGens stabReps

@[expose] def fullTree : Array (Nat × Nat × Nat) := bfsTree (Array.range 1953) #[0]

@[expose] def chkStabTree : Bool :=
  (List.range 1953).all fun a =>
    let e := stabTree[a]!
    (e.2.2 == 0 && a == stabRep (stabCls a)) ||
      (decide (0 < e.2.2) && decide (e.1 < 1953) && e.1 != 0 && tvImg e.1 0 == 0 &&
        decide (e.2.1 < 1953) && tvImg e.1 e.2.1 == a &&
        decide (stabTree[e.2.1]!.2.2 < e.2.2) && stabCls e.2.1 == stabCls a)

@[expose] def chkFullTree : Bool :=
  (List.range 1953).all fun a =>
    let e := fullTree[a]!
    (e.2.2 == 0 && a == 0) ||
      (decide (0 < e.2.2) && decide (e.1 < 1953) && decide (e.2.1 < 1953) &&
        tvImg e.1 e.2.1 == a && decide (fullTree[e.2.1]!.2.2 < e.2.2))

@[expose] def stabSizes : List Nat := [1, 30, 30, 420, 480, 480, 512]

@[expose] def chkStabCard : Bool :=
  (List.range 7).all fun c =>
    ((List.range 1953).filter fun a => stabCls a == c).length == stabSizes[c]!

@[expose] def chkStabComm : Bool :=
  let A := (List.range 1953).filter fun a => decide (stabCls a ≤ 1)
  let B := (List.range 1953).filter fun a => stabCls a == 0 || stabCls a == 2
  A.all (fun a => A.all fun b => tvImg a b == b) && B.all (fun a => B.all fun b => tvImg a b == b) &&
    tvImg 1 0 == 0 && tvImg 94 0 == 0 && tvImg 1 94 != 94

end CFSG.SmithL6
