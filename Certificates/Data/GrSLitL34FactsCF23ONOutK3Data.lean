module

public import CFSG.Sporadic.Schreier.ONCheckLocalInputs
public import Certificates.Data.GrSLitL34FactsCF23ONOutK1Data
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

abbrev Pt3 : Type := Nat × Nat × Nat

@[expose] def map3 (f : Nat → Nat) (t : Pt3) : Pt3 := (f t.1, f t.2.1, f t.2.2)

@[expose] def base3 : Pt3 := (0, 227759, 100817)

@[expose] def sigStrong : Array (Array Nat) :=
  strongArrs nPts (wordArr wA) (wordArr wB) Data.strongWords

@[expose] def sigStrongInv : Array (Array Nat) := pinvs nPts sigStrong

@[expose] def hArrs : Array (Array Nat) := wordArrs Data.MWords

@[expose] def vArrs : Array (Array Nat) := pwords nPts sigStrong sigStrongInv Data.MWords

@[expose] def zArr : Array Nat := wordArr Data.zWord

@[expose] def arrStep (A : Array (Array Nat)) (l : Nat) (t : Pt3) : Pt3 :=
  map3 (fun p => A[l]![p]!) t

@[expose] def bfs3 (ng : Nat) (step : Nat → Pt3 → Pt3) (start : Pt3) (bound : Nat) :
    Array Nat × Array Nat × Array Pt3 := Id.run do
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut im : Array Pt3 := #[start]
  let mut seen : Std.HashSet Pt3 := (∅ : Std.HashSet Pt3).insert start
  let mut h := 0
  for _ in [0:bound] do
    if h < im.size then
      let x := im[h]!
      for l in [0:ng] do
        let t := step l x
        if !seen.contains t then
          seen := seen.insert t
          par := par.push h
          lab := lab.push l
          im := im.push t
      h := h + 1
  return (par, lab, im)

@[expose] def treeOK (n ng : Nat) (step : Nat → Pt3 → Pt3) (start : Pt3) (par lab : Array Nat)
    (im : Array Pt3) : Bool :=
  im[0]! == start && allBelowN n fun k =>
    k == 0 || (decide (par[k]! < k) && decide (lab[k]! < ng) &&
      im[k]! == step lab[k]! im[par[k]!]!)

@[expose] def treeTriples (step : Nat → Pt3 → Pt3) (start : Pt3) (par lab : Array Nat)
    (n : Nat) : Array Pt3 := Id.run do
  let mut s : Array Pt3 := #[start]
  for k in [1:n] do
    s := s.push (step lab[k]! s[par[k]!]!)
  return s

@[expose] def posMap3 (im : Array Pt3) : Std.HashMap Pt3 Nat := Id.run do
  let mut m : Std.HashMap Pt3 Nat := ∅
  for k in [0:im.size] do
    m := m.insert im[k]! k
  return m

@[expose] def distinctOK (n : Nat) (im : Array Pt3) : Bool :=
  let m := posMap3 im
  allBelowN n fun k => m.getD im[k]! n == k

@[expose] def pathEval (A : Array (Array Nat)) (par lab : Array Nat) (k p : Nat) : Nat :=
  if _h : 0 < k ∧ par[k]! < k then A[lab[k]!]![pathEval A par lab par[k]! p]! else p
termination_by k
decreasing_by exact _h.2

@[expose] def mTree : Array Nat × Array Nat × Array Pt3 := bfs3 3 (arrStep hArrs) base3 161280

@[expose] def mPar : Array Nat := mTree.1

@[expose] def mLab : Array Nat := mTree.2.1

@[expose] def mIm : Array Pt3 := mTree.2.2

@[expose] def mSim : Array Pt3 := treeTriples (arrStep vArrs) base3 mPar mLab 161280

@[expose] def tTest (k : Nat) : Bool := map3 (pathEval hArrs mPar mLab k) mSim[k]! == base3

@[expose] def tList : List Nat := (List.range 161280).filter tTest

@[expose] def evalW (A : Array (Array Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun a q => A[a]![q]!) p

@[expose] def fw : Array (List Nat) :=
  #[[1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 0], [1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2]]

@[expose] def fStep (l : Nat) (t : Pt3) : Pt3 := map3 (evalW hArrs fw[l]!) t

@[expose] def fTree : Array Nat × Array Nat × Array Pt3 := bfs3 2 fStep base3 60

@[expose] def fPar : Array Nat := fTree.1

@[expose] def fLab : Array Nat := fTree.2.1

@[expose] def fIm : Array Pt3 := fTree.2.2

@[expose] def fMap : Std.HashMap Pt3 Nat := posMap3 fIm

@[expose] def fClosedOK : Bool := allBelowN 60 fun j => allBelowN 2 fun l =>
  decide (fMap.getD (fStep l fIm[j]!) 60 < 60) &&
    fIm[fMap.getD (fStep l fIm[j]!) 60]! == fStep l fIm[j]!

@[expose] def zIm : Pt3 := map3 (fun p => zArr[p]!) base3

@[expose] def fNoZOK : Bool := allBelowN 60 fun j => !(fIm[j]! == zIm)

@[expose] def fFixOK : Bool := allBelowN 2 fun l =>
  map3 (evalW vArrs fw[l]!) base3 == map3 (evalW hArrs fw[l]!) base3

@[expose] def commX : Array (List Nat) := #[[1], [1, 1, 1]]

@[expose] def commY : Array (List Nat) := #[[1, 1, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0, 1, 0, 0]]

@[expose] def evalFW (w : List Nat) (p : Nat) : Nat := w.foldr (fun a q => evalW hArrs fw[a]! q) p

@[expose] def fCommOK : Bool := allBelowN 2 fun l =>
  map3 (fun p => evalFW commX[l]! (evalFW commY[l]! p)) base3 ==
    map3 (fun p => evalW hArrs fw[l]! (evalFW commY[l]! (evalFW commX[l]! p))) base3

@[expose] def zfIm : Array Pt3 := fIm.map (map3 fun p => zArr[p]!)

@[expose] def zfMap : Std.HashMap Pt3 Nat := posMap3 zfIm

@[expose] def cTest (k : Nat) : Bool :=
  !(mSim[k]! == mIm[k]!) ||
    (decide (fMap.getD mIm[k]! 60 < 60) && fIm[fMap.getD mIm[k]! 60]! == mIm[k]!) ||
    (decide (zfMap.getD mIm[k]! 60 < 60) && zfIm[zfMap.getD mIm[k]! 60]! == mIm[k]!)

end CFSG.ComponentClassification.SolMax.ONOut
