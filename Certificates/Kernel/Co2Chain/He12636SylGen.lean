module

public meta import Certificates.Kernel.SporSch.HeT.CntData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public import Certificates.Kernel.SporSch.HeT.CntData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs

public section

namespace CertificateChecks.KernelCo2Chain.He12636Syl

open CertificateChecks.KernelSporSch.HeCn CertificateChecks.KernelSporSch.HeO16
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.Monster.B.Co2.Native

meta def comp (a b : Array Nat) : Array Nat := (Array.range 8330).map fun x => a[b[x]!]!

meta def nfPerm (nf : Array Nat) : Array Nat := (Array.range 8330).map (ev nf)

meta def idP : Array Nat := Array.range 8330

meta def hits (X Y : Array Nat) (lim : Nat) : Array (Array Nat) := Id.run do
  let L0 := lv[0]!
  let L1 := lv[1]!
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  let mut out : Array (Array Nat) := #[]
  for k0 in [0:L0.pts.size] do
    let t0 := L0.tr[k0]!
    let t0i := L0.trInv[k0]!
    let p0 := t0[0]!
    if Y[p0]! == p0 then
      for k1 in [0:L1.pts.size] do
        let t1 := L1.tr[k1]!
        let t1i := L1.trInv[k1]!
        let q := t0[t1[1]!]!
        let v := t1i[t0i[Y[q]!]!]!
        let k2 := L2.pos[v]!
        if k2 < L2.pts.size then
          for k3 in [0:L3.pts.size] do
            for k4 in [0:L4.pts.size] do
              let nf := #[k0, k1, k2, k3, k4]
              if [0, 1, 2, 3, 4].all (fun b => ev nf X[b]! == Y[ev nf b]!) then
                out := out.push nf
                if out.size ≥ lim then
                  return out
  return out

meta def closure (gens : Array (Array Nat)) (cap : Nat) :
    Array (Array Nat × Nat × Nat × Nat) := Id.run do
  let mut els : Array (Array Nat × Nat × Nat × Nat) := #[(idP, 0, 0, 0)]
  let mut i := 0
  while i < els.size && els.size ≤ cap do
    let (e, _, _, d) := els[i]!
    for j in [0:gens.size] do
      let p := comp e gens[j]!
      if !(els.any fun r => r.1 == p) then
        els := els.push (p, i, j, d + 1)
    i := i + 1
  return els

meta def yA : Array Nat := heThreeBA
meta def cA : Array Nat := nfPerm (cOf yA)
meta def xA : Array Nat := xOf yA

meta def gensM : Array (Array Nat) := Id.run do
  let ci := invCand 8330 cA
  let X := xA
  let Y := yA
  let e1 : Array (Array Nat) := #[idP, yA, comp yA yA]
  let mut u := idP
  let mut e2 : Array (Array Nat) := #[]
  let L0 := lv[0]!
  let L1 := lv[1]!
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  for k0 in [0:L0.pts.size] do
    let t0 := L0.tr[k0]!
    let t0i := L0.trInv[k0]!
    let p0 := t0[0]!
    if Y[p0]! == p0 then
      for k1 in [0:L1.pts.size] do
        let t1 := L1.tr[k1]!
        let t1i := L1.trInv[k1]!
        let q := t0[t1[1]!]!
        let w := t1i[t0i[Y[q]!]!]!
        let k2 := L2.pos[w]!
        if k2 < L2.pts.size then
          for k3 in [0:L3.pts.size] do
            for k4 in [0:L4.pts.size] do
              let nf := #[k0, k1, k2, k3, k4]
              if [0, 1, 2, 3, 4].all (fun b => ev nf X[b]! == Y[ev nf b]!) then
                let hp (x : Nat) : Nat := ev nf ci[x]!
                if (List.range 40).all fun x => hp (hp (hp x)) == x then
                  let h := comp (nfPerm nf) ci
                  if comp h (comp h h) == idP then
                    if u == idP then
                      if !(e1.any (· == h)) then
                        u := h
                        e2 := (closure #[yA, u] 9).map (·.1)
                    else if !(e2.any (· == h)) &&
                        e2.any (· == comp h (comp u (invCand 8330 h))) then
                      if (closure #[yA, u, h] 27).size == 27 then
                        return #[yA, u, h]
  return #[yA, u, idP]

meta def keyOf (e : Array Nat) : Nat :=
  (List.range 5).foldl (fun acc b => acc ||| (e[b]! <<< (14 * b))) 0

meta def sylM : Array (Array Nat × Nat × Nat × Nat) := closure gensM 27

meta def ordM : Array Nat :=
  (Array.range sylM.size).qsort fun a b => keyOf sylM[a]!.1 < keyOf sylM[b]!.1

meta def posM : Array Nat := Id.run do
  let mut p := Array.replicate sylM.size 0
  for i in [0:ordM.size] do
    p := p.set! ordM[i]! i
  return p

meta def conjOf (s : Array Nat) : Nat × Nat :=
  let fx := (List.range 8330).countP fun x => s[x]! == x
  let bit := if fx == 77 then 0 else 1
  let Y := if bit == 0 then heThreeBA else heThreeBB
  let cs := nfPerm (cOf s)
  let xs := comp (invCand 8330 cs) (comp s cs)
  let cX := nfPerm (cOf Y)
  let xX := xOf Y
  let g := nfPerm ((hits xs xX 1).getD 0 #[0, 0, 0, 0, 0])
  let G := comp cX (comp g (invCand 8330 cs))
  (nfOf G, bit)

meta def packW (w : Nat) (vs : List Nat) : Nat :=
  (List.range vs.length).foldl (fun acc i => acc ||| (vs[i]! <<< (w * i))) 0

meta def natsM : List Nat :=
  let n := sylM.size
  let el (i : Nat) : Array Nat := sylM[ordM[i]!]!.1
  let gens := gensM
  let gIdx := gens.toList.map fun g => ((List.range n).find? fun i => el i == g).getD 0
  let root := posM[0]!
  let cj := (List.range n).map fun i => if i == root then (0, 0) else conjOf (el i)
  let mt := (List.range 3).flatMap fun j => (List.range n).map fun i =>
    let p := comp (el i) gens[j]!
    ((List.range n).find? fun k => el k == p).getD 0
  let rec_ (i : Nat) : Array Nat × Nat × Nat × Nat := sylM[ordM[i]!]!
  [packW 80 ((List.range n).map fun i => nfOf (el i)), packW 80 (cj.map (·.1)),
    packW 1 (cj.map (·.2)), packW 5 mt,
    packW 5 ((List.range n).map fun i => posM[(rec_ i).2.1]!),
    packW 5 ((List.range n).map fun i => (rec_ i).2.2.1),
    packW 5 ((List.range n).map fun i => (rec_ i).2.2.2), packW 5 gIdx, root]

end CertificateChecks.KernelCo2Chain.He12636Syl

end
