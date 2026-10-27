module

public meta import Certificates.Data.MaxD2Perm
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.KS.MaxD2.Gen

open CFSG.PSL3Four.Native Certificates.MaxD2Perm

meta def key (w : Nat) (vs : List Nat) : Nat :=
  (vs.zipIdx).foldl (fun acc (v, t) => acc ||| (v <<< (w * t))) 0

meta def fpKey (w : Nat) (pts : List Nat) (a : Tab) : Nat := key w (pts.map fun b => a[b]!)

structure Pre where
  nT : Array Tab
  rT : Array Tab
  rep : Array Tab
  repi : Array Tab
  keys : Array Nat
  order : Array Nat

meta def pre (D : Data) (w : Nat) : Pre :=
  let nT := (nEnum D).tabs
  let keys := nT.map (fpKey w D.fpPts)
  let order := (List.range nT.size).toArray.qsort fun a b => keys[a]! < keys[b]!
  { nT, rT := (rEnum D).tabs, rep := repT D, repi := repI D, keys, order }

meta def fpSort (P : Pre) : Array Nat := P.order

meta def fpKeys (P : Pre) : Array Nat := P.order.map fun e => P.keys[e]!

meta def repImgs (D : Data) (P : Pre) : Array Nat :=
  (P.rep.map fun g => (D.fpPts.map fun b => g[b]!).toArray).flatten

meta partial def lowerBound (ks : Array Nat) (y : Nat) : Nat :=
  go 0 ks.size
where
  go (lo hi : Nat) : Nat :=
    if lo < hi then
      let mid := (lo + hi) / 2
      if ks[mid]! < y then go (mid + 1) hi else go lo mid
    else lo

meta def hint (D : Data) (w : Nat) (P : Pre) (ks : Array Nat) (g gi a : Tab) : Nat :=
  let n := D.n
  let y := comp n (comp n gi a) g
  let yk := fpKey w D.fpPts y
  let q := lowerBound ks yk
  if q < ks.size && ks[q]! == yk then
    let e := P.order[q]!
    if P.nT[e]! == y then 2 * e + 1
    else
      let p := ((List.range n).find? fun x => y[x]! != (P.nT[e]!)[x]!).getD 0
      4 * q + 2 + (p <<< 18)
  else 4 * q

meta def hints (D : Data) (w : Nat) (P : Pre) : Array Nat :=
  let ks := fpKeys P
  ((List.range P.rep.size).toArray.map fun i =>
    if i == 0 then Array.replicate P.nT.size 0
    else P.nT.map fun a => hint D w P ks P.rep[i]! P.repi[i]! a).flatten

meta def counts (D : Data) (w : Nat) (P : Pre) : Array Nat :=
  let h := hints D w P
  let c := P.nT.size
  (List.range P.rep.size).toArray.map fun i =>
    if i == 0 then c else ((List.range c).filter fun k => h[c * i + k]! % 2 == 1).length

meta def centHints (D : Data) (P : Pre) : Array Nat :=
  let n := D.n
  let u := (rGens D)[0]!
  let v := (rGens D)[1]!
  let rIdx := indexOf P.rT
  P.nT.map fun a =>
    let diff := fun (g : Tab) => (List.range n).find? fun p => a[g[p]!]! != g[a[p]!]!
    match diff u with
    | some p => 4 * p
    | none => match diff v with
      | some p => 4 * p + 2
      | none => 2 * (rIdx.getD a 0) + 1

meta def normHints (D : Data) (P : Pre) : Array Nat :=
  let n := D.n
  let rIdx := indexOf P.rT
  let gs := nGens D
  let gi := nGensI D
  let rs := rGens D
  ((List.range gs.size).toArray.map fun j => ((List.range rs.size).toArray.map fun i =>
    #[rIdx.getD (conjTab n gs[j]! gi[j]! rs[i]!) 0,
      rIdx.getD (conjTab n gi[j]! gs[j]! rs[i]!) 0]).flatten).flatten

meta def torusPos (D : Data) (P : Pre) : Nat := (indexOf P.nT).getD (wT D D.tW) 0

meta def labels (D : Data) : Array Nat := Id.run do
  let n := D.n
  let gs := nGens D
  let mut lab := Array.replicate n n
  let mut nl := 0
  for x in [0:n] do
    if lab[x]! == n then
      lab := lab.set! x nl
      let mut stack := #[x]
      while !stack.isEmpty do
        let y := stack.back!
        stack := stack.pop
        for g in gs do
          let z := g[y]!
          if lab[z]! == n then
            lab := lab.set! z nl
            stack := stack.push z
      nl := nl + 1
  return lab

meta def numLabels (D : Data) : Nat := (labels D).foldl (fun m l => max m (l + 1)) 0

meta def mkeys (D : Data) (cw : Nat) (P : Pre) : Array Nat :=
  let L := labels D
  let nl := numLabels D
  P.rep.map fun g => (List.range D.n).foldl
    (fun s y => s + (1 <<< (cw * (nl * L[g[y]!]! + L[y]!)))) 0

meta def movesWit (D : Data) (P : Pre) : Nat :=
  let n := D.n
  let rIdx := indexOf P.rT
  let rs := rGens D
  ((List.range D.gT.size).flatMap fun j => (List.range rs.size).map fun i => (j, i)).find?
    (fun (j, i) => !found rIdx P.rT (conjTab n D.gT[j]! (giT D)[j]! rs[i]!)) |>.map
    (fun (j, i) => 2 * j + i) |>.getD 0

end CFSG.KS.MaxD2.Gen

end
