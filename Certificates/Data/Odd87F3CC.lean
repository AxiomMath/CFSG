module

public import Certificates.Data.Odd87F3Check
public meta import Certificates.Data.Odd87F3Check

public section

namespace Certificates.Odd87F3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

structure Orb where
  base : ℕ
  y0 : ℕ
  sg : List (List ℤ)
  ns : List (List ℤ)

@[expose] def decodeLetter (c : Char) : ℤ :=
  if 97 ≤ c.toNat ∧ c.toNat ≤ 105 then ((c.toNat - 96 : ℕ) : ℤ)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 73 then -((c.toNat - 64 : ℕ) : ℤ) else 0

@[expose] def decodeWords (s : String) : List (List ℤ) :=
  ((s.splitOn " ").filter fun t => t.length > 0).map fun t => t.toList.map decodeLetter

@[expose] def decodeCov (s : String) : List (ℕ × List ℤ) :=
  ((s.splitOn " ").filter fun t => t.length > 0).map fun t =>
    (t.toList.head!.toNat - 48, t.toList.tail.map decodeLetter)

@[expose] def ccOK (n : ℕ) (gT : List Table) (orbs : List Orb) (cov : List (ℕ × List ℤ)) : Bool :=
  let gIT := gT.map (invT n)
  gT.all (fun g => invOK n g (invT n g)) &&
    orbs.all (fun o =>
      let SG := o.sg.map (evalT n gT gIT)
      let NS := o.ns.map (evalT n gT gIT)
      decide (o.base < n) && decide (o.y0 < n) &&
        SG.all (fun T => ap T o.base == o.base) && NS.all (fun T => ap T o.base != o.base) &&
        (List.range n).all fun y =>
          !(SG.all (fun T => ap T y == y) && NS.all (fun T => ap T y != y)) ||
            y == o.base || y == o.y0) &&
    (List.range n).all fun v =>
      match cov[v]? with
      | none => false
      | some (i, w) =>
        match orbs[i]? with
        | none => false
        | some o => ap (evalT n gT gIT w) o.base == v

end Certificates.Odd87F3
