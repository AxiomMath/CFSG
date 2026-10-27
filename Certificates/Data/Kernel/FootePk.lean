module

public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public import CFSG.GH74.KGroups.PermCheck
public import Mathlib

public section

namespace CFSG.Certificates.Kernel.FootePk

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.PK

variable {n : Nat}

@[expose] def eqV (a b : VP n) : Bool :=
  (List.range n).all fun i => fd (wd n) a.1.1 i == fd (wd n) b.1.1 i

@[expose] def powV (a : VP n) : Nat → VP n
  | 0 => oneV n
  | k + 1 => mulV (powV a k) a

@[expose] def keyV (k : Nat) (g : VP n) : Nat :=
  Nat.fold k (fun i _ acc => acc * n + if _ : i < n then fd (wd n) g.1.1 i else 0) 0

@[expose] def visitV (k : Nat) (C : List (VP n)) (st : Nat × List (VP n)) (x : VP n) :
    Nat × List (VP n) :=
  C.foldl (fun st c =>
    match st with
    | (seen, found) =>
      let i := keyV k (mulV x c)
      if seen.testBit i then (seen, found) else (seen ||| 1 <<< i, mulV x c :: found)) st

@[expose] def searchV (k : Nat) (C : List (VP n)) :
    Nat → Nat → List (VP n) → List (VP n) → List (VP n)
  | 0, _, _, acc => acc
  | fuel + 1, seen, frontier, acc =>
    match frontier.foldl (visitV k C) (seen, []) with
    | (_, []) => acc
    | (seen', found) => searchV k C fuel seen' found (found ++ acc)

@[expose] def genCheckV (k : Nat) (C targets : List (VP n)) : Bool :=
  let L := searchV k C 64 (1 <<< keyV k (oneV n)) [oneV n] [oneV n]
  targets.all fun g => L.any fun x => eqV g x

@[expose] def commBV (c t : VP n) : Bool :=
  (List.range n).all fun i =>
    fd (wd n) c.1.1 (fd (wd n) t.1.1 i) == fd (wd n) t.1.1 (fd (wd n) c.1.1 i)

@[expose] def dihBV (u v : VP n) : Bool :=
  eqV (mulV u u) (oneV n) && eqV (mulV v v) (oneV n) && !eqV (mulV u v) (mulV v u) &&
    eqV (powV (mulV u v) 4) (oneV n)

@[expose] def dihInvsV (u v : VP n) : List (VP n) :=
  [u, v, mulV (mulV u v) u, mulV (mulV v u) v, powV (mulV u v) 2]

@[expose] def pairCheckV (k m : Nat) (Q LP targets : List (VP n)) : Bool :=
  Q.all fun u => Q.all fun v =>
    !dihBV u v ||
      genCheckV k ((dihInvsV u v).flatMap fun t =>
        CFSG.ComponentClassification.FooteSmall.spread m (LP.filter fun c => commBV c t)) targets

end CFSG.Certificates.Kernel.FootePk

end
