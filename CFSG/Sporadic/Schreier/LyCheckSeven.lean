module

public import CFSG.Sporadic.Schreier.LyCheckCover

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def uArr : Array (Array Nat) :=
  Array.ofFn (n := 111) fun j => Array.ofFn (n := 7) fun m => bpRootArr[111 * m.val + j.val]!

@[expose] def mulXU (X : Mat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 7) fun m =>
    (Nat.fold 111 (fun k _ acc => acc + X[i.val]![k]! * uArr[k]![m.val]!) 0) % 5

@[expose] def restrArr (X : Mat) : Array Nat :=
  let Y := mulXU X
  Array.ofFn (n := 49) fun t => Y[t.val / 7]![t.val % 7]!

@[expose] def mulUR (R : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 111) fun i => Array.ofFn (n := 7) fun c =>
    (Nat.fold 7 (fun m _ acc => acc + uArr[i.val]![m]! * R[7 * m + c.val]!) 0) % 5

@[expose] def stabOK (X : Mat) : Bool := mulXU X == mulUR (restrArr X)

@[expose] def strongWordsTail : List (List Int) :=
  (List.range 5).map fun j => parseInts ((strongWordsTxt.splitOn "\n").getD (j + 2) "")

@[expose] def aStarArr (b4 : Mat) : Array (Mat × Mat) :=
  extendM #[(matA, matA), (matB, b4)] strongWordsTail

@[expose] def mv7 (R v : Array Nat) : Array Nat :=
  Array.ofFn (n := 7) fun r => (Nat.fold 7 (fun c _ acc => acc + R[7 * r.val + c]! * v[c]!) 0) % 5

@[expose] def stdVec (i : Nat) : Array Nat :=
  Array.ofFn (n := 7) fun r => if r.val = i then 1 else 0

@[expose] def code7 (v : Array Nat) : Nat := Nat.fold 7 (fun c _ acc => acc + v[c]! * 5 ^ c) 0

@[expose] def dagArr (gens : Nat → Array Nat) : Array (Array Nat) :=
  hDag.foldl (fun vals e =>
    vals.push (if e.1 = 0 then gens e.2.1 else if e.1 = 1 then inv7 (vals.getD e.2.1 id7)
      else mul7 (vals.getD e.2.1 id7) (vals.getD e.2.2 id7))) #[]

@[expose] def dagLocalOK (gens : Nat → Array Nat) (vals : Array (Array Nat)) : Bool :=
  allIn 0 hDag.size fun k =>
    let e := hDag[k]!
    vals[k]! == (if e.1 = 0 then gens e.2.1 else if e.1 = 1 then inv7 (vals.getD e.2.1 id7)
      else mul7 (vals.getD e.2.1 id7) (vals.getD e.2.2 id7))

@[expose] def dagInvOK (vals : Array (Array Nat)) : Bool :=
  allIn 0 hDag.size fun k =>
    let e := hDag[k]!
    e.1 != 1 || mul7 (vals.getD e.2.1 id7) vals[k]! == id7

@[expose] def vecBFS (root : Array Nat) (gens : Array (Array Nat)) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut seen : Array Bool := (Array.replicate 78125 false).set! (code7 root) true
  let mut pts : Array (Array Nat) := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:78125] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:gens.size] do
        let y := mv7 gens[j]! x
        if !seen[code7 y]! then
          seen := seen.set! (code7 y) true
          pts := pts.push y
          par := par.push h
          lab := lab.push j
  return (pts, par, lab)

@[expose] def vecTreeOK (root : Array Nat) (gens : Array (Array Nat))
    (T : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let pts := T.1
  let par := T.2.1
  let lab := T.2.2
  let index : Std.HashMap (Array Nat) Nat :=
    (List.range pts.size).foldl (fun m k => m.insert pts[k]! k) ∅
  par.size == pts.size && lab.size == pts.size && pts[0]! == root &&
    (pts.all fun v => v.size == 7 && v.all (· < 5)) &&
    allIn 1 pts.size (fun k => par[k]! < k && lab[k]! < gens.size &&
      mv7 gens[lab[k]!]! pts[par[k]!]! == pts[k]!) &&
    allIn 0 pts.size (fun k => index.getD pts[k]! pts.size == k)

@[expose] def levelFixOK (gens : Array (Array Nat)) (i : Nat) : Bool :=
  gens.all fun R => allIn 0 i fun l => mv7 R (stdVec l) == stdVec l

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

@[expose] def hGenPairs (as : Array (Mat × Mat)) : Array (Array Nat × Array Nat) :=
  Array.ofFn (n := 5) fun j =>
    let R := restrArr (pairAt as (j.val + 2)).1
    (R, inv7 R)

@[expose] def sevenCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  let as := aStarArr b4
  let gens := fun j => restrArr (pairAt as (j + 2)).1
  let vals := dagArr gens
  let lv := fun i => ((hLevelGens.getD i []).map fun k => vals.getD k id7).toArray
  let T0 := vecBFS (stdVec 0) (lv 0)
  let T1 := vecBFS (stdVec 1) (lv 1)
  let T2 := vecBFS (stdVec 2) (lv 2)
  let v := evalWordM seedM (seedMInv b4) transporterWord
  let vi := invM 5 111 v
  let t := mulM 5 111 (mulM 5 111 vi matA) v
  let Rt := restrArr t
  let hp := hGenPairs as
  let C := conjBFS Rt hp 406875
  mulM 5 111 matB b4 == idM 111 && as.size == 7 && invPairsOK as &&
    allIn 2 7 (fun j => actKey (frTable (pairAt as j).1) bpRootKey == some bpRootKey &&
      stabOK (pairAt as j).1) &&
    vals.size == hDag.size && dagLocalOK gens vals && dagInvOK vals &&
    (allIn 0 hDag.size fun k => hDag[k]!.1 == 0 ||
      (hDag[k]!.2.1 < k && (hDag[k]!.1 == 1 || hDag[k]!.2.2 < k))) &&
    levelFixOK (lv 1) 1 && levelFixOK (lv 2) 2 &&
    vecTreeOK (stdVec 0) (lv 0) T0 && T0.1.size == 15624 &&
    vecTreeOK (stdVec 1) (lv 1) T1 && T1.1.size == 3125 &&
    vecTreeOK (stdVec 2) (lv 2) T2 && T2.1.size == 120 &&
    mulM 5 111 v vi == idM 111 &&
    (hp.all fun p => mul7 p.1 p.2 == id7) &&
    conjTreeOK Rt hp C && 406875 ≤ C.1.size

end CFSG.Sporadic.LySchreier.Native
