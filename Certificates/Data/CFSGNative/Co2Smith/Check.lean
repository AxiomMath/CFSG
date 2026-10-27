module

public import Certificates.Data.CFSGNative.Co2Smith.Words
public import Certificates.Data.CFSGNative.Co2Smith.Data
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native

set_option compiler.extract_closed false

@[expose] def letters (seeds : Array (Array Nat)) : Array (Array Nat) :=
  #[seeds[0]!, seeds[1]!, wRows seeds aWord, wRows seeds bWord]

@[expose] def encM (X : Array Nat) : Nat := X.foldr (fun r acc => acc * 4194304 + r) 0

@[expose] def validM (X : Array Nat) : Bool := X.size == 22 && X.all (· < 4194304)

@[expose] def subId (M : Array Nat) : Array Nat := (List.range 22).toArray.map fun i =>
  M[i]! ^^^ (1 <<< i)

@[expose] def invOK (A : Array Nat) : Bool :=
  mulRows 22 (mulRows 22 (transposeRows 22 A) betaRows) A == betaRows

@[expose] def betaOK (seeds : Array (Array Nat)) : Bool := invOK seeds[0]! && invOK seeds[1]!

@[expose] def conjSeed (seeds : Array (Array Nat)) (l : Nat) (X : Array Nat) : Array Nat :=
  if l == 0 then mulRows 22 (mulRows 22 seeds[0]! X) seeds[0]!
  else mulRows 22 (mulRows 22 seeds[1]! X) (powRows 22 seeds[1]! 4)

@[expose] def classBFS (seeds : Array (Array Nat)) (X0 : Array Nat) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (encM X0) 0
  let mut els : Array (Array Nat) := #[X0]
  let mut par : Array Nat := #[0]
  let mut let_ : Array Nat := #[0]
  let mut i := 0
  for _ in [0:cap] do
    if i < els.size then
      let X := els[i]!
      for l in [0:2] do
        let Y := conjSeed seeds l X
        let e := encM Y
        if !seen.contains e then
          seen := seen.insert e els.size
          els := els.push Y
          par := par.push i
          let_ := let_.push l
      i := i + 1
  return (els, par, let_)

@[expose] def posMap (els : Array (Array Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:els.size] do
    m := m.insert (encM els[i]!) i
  return m

@[expose] def classCertOK (seeds : Array (Array Nat)) (X0 : Array Nat) (n : Nat)
    (rec : Array (Array Nat) × Array Nat × Array Nat) : Bool :=
  let els := rec.1
  let par := rec.2.1
  let let_ := rec.2.2
  let pm := posMap els
  let pos := fun (X : Array Nat) => pm.getD (encM X) els.size
  els.size == n && par.size == n && let_.size == n && els[0]! == X0 &&
    (List.range n).all fun i =>
      validM els[i]! && pos els[i]! == i &&
      (i == 0 ||
        (par[i]! < i && let_[i]! < 2 && els[i]! == conjSeed seeds let_[i]! els[par[i]!]!)) &&
      (List.range 2).all fun l =>
        let Y := conjSeed seeds l els[i]!
        pos Y < n && els[pos Y]! == Y

@[expose] def classOK (seeds : Array (Array Nat)) : Bool :=
  classCertOK seeds seeds[0]! 56925 (classBFS seeds seeds[0]! 60000)

@[expose] def mRows (seeds : Array (Array Nat)) (w : List Nat) : Array Nat :=
  wRows (letters seeds) w

@[expose] def commRows (X Y : Array Nat) : Bool := mulRows 22 X Y == mulRows 22 Y X

@[expose] def hypC (i j : Nat) : Bool := i + 4 == j || j + 4 == i

@[expose] def hRows (seeds : Array (Array Nat)) : Array (Array Nat) := hWords.map (mRows seeds)

@[expose] def nfRows (seeds : Array (Array Nat)) (H : Array (Array Nat)) (s v : Nat) :
    Array Nat :=
  let m := (List.range 8).foldr (fun i acc => if v.testBit i then mulRows 22 H[i]! acc else acc)
    (idRows 22)
  if s == 1 then mulRows 22 seeds[0]! m else m

@[expose] def strictIncr : List Nat → Bool
  | a :: b :: l => a < b && strictIncr (b :: l)
  | _ => true

@[expose] def elementsOK (seeds : Array (Array Nat)) : Bool :=
  let z := seeds[0]!
  let zm := subId z
  let a := mRows seeds [2]
  let b := mRows seeds [3]
  let H := hRows seeds
  powRows 22 a 3 == idRows 22 && powRows 22 b 7 == idRows 22 &&
    commRows a z && commRows b z && colAct a wFix == wFix && colAct b wFix == wFix &&
    H.size == 8 &&
    (List.range 8).all (fun i =>
      mulRows 22 H[i]! H[i]! == idRows 22 && commRows H[i]! z && mulRows 22 H[i]! zm == zm &&
      (List.range 8).all fun j =>
        mulRows 22 H[i]! H[j]! ==
          (if hypC i j then mulRows 22 (mulRows 22 H[j]! H[i]!) z else mulRows 22 H[j]! H[i]!)) &&
    (let sigs := (List.range 2).flatMap fun s => (List.range 256).map fun v =>
        let m := nfRows seeds H s v
        colAct m wFix * 4194304 + colAct m sepVec
      let sorted := sigs.mergeSort (fun x y => decide (x ≤ y))
      sorted.length == 512 && strictIncr sorted) &&
    (List.range 2).all fun s => (List.range 255).all fun v =>
      colAct (nfRows seeds H s (v + 1)) wFix != wFix

@[expose] def orbitBFS (step : Nat → Nat → Nat) (ngen : Nat) (start cap : Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert start 0
  let mut pts : Array Nat := #[start]
  let mut par : Array Nat := #[0]
  let mut let_ : Array Nat := #[0]
  let mut i := 0
  for _ in [0:cap] do
    if i < pts.size then
      let x := pts[i]!
      for l in [0:ngen] do
        let y := step l x
        if !seen.contains y then
          seen := seen.insert y pts.size
          pts := pts.push y
          par := par.push i
          let_ := let_.push l
      i := i + 1
  return (pts, par, let_)

@[expose] def posMapN (pts : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:pts.size] do
    m := m.insert pts[i]! i
  return m

@[expose] def treeOK (step : Nat → Nat → Nat) (ngen : Nat) (start n : Nat) (closed : Bool)
    (rec : Array Nat × Array Nat × Array Nat) : Bool :=
  let pts := rec.1
  let par := rec.2.1
  let let_ := rec.2.2
  let pm := posMapN pts
  let pos := fun (x : Nat) => pm.getD x pts.size
  pts.size == n && par.size == n && let_.size == n && pts[0]! == start &&
    (List.range n).all fun i =>
      pos pts[i]! == i &&
      (i == 0 || (par[i]! < i && let_[i]! < ngen && pts[i]! == step let_[i]! pts[par[i]!]!)) &&
      (!closed || (List.range ngen).all fun l =>
        let y := step l pts[i]!
        pos y < n && pts[pos y]! == y)

@[expose] def pairStep (G : Array (Array Nat)) (l x : Nat) : Nat :=
  colAct G[l]! (x / 4194304) * 4194304 + colAct G[l]! (x % 4194304)

@[expose] def pairOK (seeds : Array (Array Nat)) : Bool :=
  let G := #[mRows seeds [2], mRows seeds [3]]
  let start := pairU * 4194304 + pairV
  let rec_ := orbitBFS (pairStep G) 2 start 20000
  let n := rec_.1.size
  let z := seeds[0]!
  treeOK (pairStep G) 2 start n true rec_ &&
    !rec_.1.contains (colAct z pairU * 4194304 + colAct z pairV) && pairU < 4194304 &&
    pairV < 4194304 && rec_.1.all (· < 17592186044416)

@[expose] def vecStep (G : Array (Array Nat)) (l x : Nat) : Nat := colAct G[l]! x

@[expose] def chainOK (seeds : Array (Array Nat)) : Bool :=
  chainGens.size == 6 && chainBase.length == 6 && chainOrb.length == 6 &&
  (List.range 6).all fun k =>
    let G := chainGens[k]!.map (mRows seeds)
    let base := chainBase[k]!
    (List.range k).all (fun j => G.all fun g => colAct g chainBase[j]! == chainBase[j]!) &&
      treeOK (vecStep G) G.size base chainOrb[k]! false
        (orbitBFS (vecStep G) G.size base 100)

@[expose] def fRows (seeds : Array (Array Nat)) : Array (Array Nat) :=
  frameWords.map (mRows seeds)

@[expose] def conjTo (P X Y : Array Nat) : Bool := mulRows 22 P X == mulRows 22 Y P

@[expose] def frameOK (seeds : Array (Array Nat)) : Bool :=
  let F := fRows seeds
  let I := idRows 22
  let sw := fun (i : Nat) => if i == 0 then 1 else if i == 1 then 0 else i
  let sw' := fun (i : Nat) => if i == 1 then 2 else if i == 2 then 1 else i
  F.size == 10 &&
  (List.range 3).all (fun i =>
    let y := F[2 * i]!
    let s := F[2 * i + 1]!
    powRows 22 y 3 == I && mulRows 22 s s == I &&
      mulRows 22 (mulRows 22 s y) s == mulRows 22 y y) &&
  (List.range 3).all (fun i => (List.range 3).all fun j => i == j ||
    (List.range 2).all fun e => (List.range 2).all fun e' =>
      commRows F[2 * i + e]! F[2 * j + e']!) &&
  (List.range 6).all (fun k =>
    conjTo F[6]! F[k]! F[2 * sw (k / 2) + k % 2]! &&
      conjTo F[7]! F[k]! F[2 * sw' (k / 2) + k % 2]!) &&
  powRows 22 F[8]! 5 == I && commRows F[8]! F[0]! && commRows F[8]! F[1]! &&
  mulRows 22 F[9]! F[8]! == mulRows 22 (mulRows 22 F[8]! F[8]!) F[9]! &&
  commRows F[9]! F[0]! &&
  pinRels.all (fun r => powRows 22 (mulRows 22 F[8]! (wRows F r.1)) r.2 == I) &&
  wRows F genAWord == mRows seeds [2] && wRows F genBWord == mRows seeds [3]

@[expose] def parity22 (n : Nat) : Nat :=
  (List.range 22).foldl (fun acc j => if n.testBit j then 1 - acc else acc) 0

@[expose] def betaVal (u v : Nat) : Nat := parity22 (u &&& colAct betaRows v)

@[expose] def zetaComb (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => if c.testBit i then acc ^^^ zetaVecs[i]! else acc) 0

@[expose] def jPat (i j : Nat) : Nat := if i + 3 == j || j + 3 == i then 1 else 0

@[expose] def zetaOK (seeds : Array (Array Nat)) : Bool :=
  let zm := subId seeds[0]!
  zetaVecs.size == 6 && zetaPre.size == 6 &&
    (List.range 6).all (fun i => colAct zm zetaPre[i]! == zetaVecs[i]! &&
      zetaVecs[i]! < 4194304 && zetaPre[i]! < 4194304) &&
    (List.range 63).all (fun c => zetaComb (c + 1) != 0) &&
    (List.range 22).all (fun k => (List.range 64).any fun c => zetaComb c == colAct zm (1 <<< k)) &&
    (List.range 6).all fun i => (List.range 6).all fun j =>
      betaVal zetaPre[i]! zetaVecs[j]! == jPat i j

@[expose] def zetaCoord (v : Nat) : Nat := ((List.range 64).find? fun c => zetaComb c == v).getD 64

@[expose] def coordCols (M : Array Nat) : List Nat :=
  (List.range 6).map fun j => zetaCoord (colAct M zetaVecs[j]!)

@[expose] def colsA (_ : Unit := ()) : List Nat := [20, 62, 17, 26, 4, 8]

@[expose] def colsB (_ : Unit := ()) : List Nat := [31, 14, 33, 2, 3, 37]

@[expose] def resOK (seeds : Array (Array Nat)) : Bool :=
  let a := mRows seeds [2]
  let b := mRows seeds [3]
  (List.range 6).all (fun j =>
    zetaComb colsA[j]! == colAct a zetaVecs[j]! && zetaComb colsB[j]! == colAct b zetaVecs[j]!) &&
  ((List.range 6).all fun i => (List.range 64).any fun c =>
    (List.range 6).foldl (fun acc k => if c.testBit k then acc ^^^ chainBase[k]! else acc) 0 ==
      zetaVecs[i]!) &&
  (List.range 6).all fun k => (List.range 64).any fun c => zetaComb c == chainBase[k]!

@[expose] def xFpfOK (seeds : Array (Array Nat)) : Bool :=
  let H := hRows seeds
  let x := (fRows seeds)[8]!
  (List.range 2).all fun s => (List.range 255).all fun v => !commRows x (nfRows seeds H s (v + 1))

end CFSG.Sporadic.Co2Smith.Native
