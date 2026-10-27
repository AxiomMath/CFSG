module

public import Certificates.Data.CFSGNative.Ly.Orbit
public import Certificates.Data.CFSGNative.LySchreier.Check
public import Std.Data.HashMap

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.LySchreier.Native

@[expose] def conjBFS (root : Array Nat) (gens : Array (Array Nat × Array Nat)) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut index : Std.HashMap (Array Nat) Nat := (∅ : Std.HashMap _ _).insert root 0
  let mut pts : Array (Array Nat) := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:gens.size] do
        let y := mul7 (mul7 gens[j]!.1 x) gens[j]!.2
        if !index.contains y then
          index := index.insert y pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push j
  return (pts, par, lab)

@[expose] def conjTreeOK (root : Array Nat) (gens : Array (Array Nat × Array Nat))
    (T : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let pts := T.1
  let par := T.2.1
  let lab := T.2.2
  let index : Std.HashMap (Array Nat) Nat :=
    (List.range pts.size).foldl (fun m k => m.insert pts[k]! k) ∅
  par.size == pts.size && lab.size == pts.size && pts[0]! == root &&
    (pts.all fun X => X.size == 49 && X.all (· < 5)) &&
    allIn 1 pts.size (fun k => par[k]! < k && lab[k]! < gens.size &&
      mul7 (mul7 gens[lab[k]!]!.1 pts[par[k]!]!) gens[lab[k]!]!.2 == pts[k]!) &&
    allIn 0 pts.size (fun k => index.getD pts[k]! pts.size == k)

@[expose] def conjClosedOK (gens : Array (Array Nat × Array Nat))
    (T : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let pts := T.1
  let index : Std.HashMap (Array Nat) Nat :=
    (List.range pts.size).foldl (fun m k => m.insert pts[k]! k) ∅
  allIn 0 pts.size (fun k => gens.all fun g => index.contains (mul7 (mul7 g.1 pts[k]!) g.2))

@[expose] def fixSetOK (n : Nat) (T : Table) (fi : Array Nat) : Bool :=
  let m := fixedMask n fi
  allIn 0 (fi.size - 1) (fun k => fi[k]! < fi[k + 1]!) && allIn 0 fi.size (fun k => fi[k]! < n) &&
    allIn 0 n (fun i => (ap T i == i) == m[i]!)

end CFSG.RankThree.PartOne.LyFive
