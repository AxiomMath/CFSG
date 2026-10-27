module

public import Certificates.Data.CFSGNative.Th.Orbit
public import Certificates.Data.E27Table

public section

namespace Timmesfeld.PcReg

open CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def digitsOf (p n i : Nat) : Array Nat := Id.run do
  let mut a : Array Nat := Array.replicate n 0
  let mut x := i
  for t in [0:n] do
    a := a.set! (n - 1 - t) (x % p)
    x := x / p
  return a

@[expose] def unitVec (n j : Nat) : Array Nat := (Array.replicate n 0).set! j 1

@[expose] def applyWord (prev : Array (Array Nat)) (k₁ n : Nat) (ds : Array Nat) (r : Nat) :
    Nat := Id.run do
  let mut x := r
  for t in [0:n - k₁] do
    let m := n - 1 - t
    for _ in [0:ds[m]!] do
      x := (prev[m - k₁]!)[x]!
  return x

@[expose] def stepLevel (p n k : Nat) (pw cwR : Array (Array Nat)) (prev : Array (Array Nat)) :
    Array (Array Nat) := Id.run do
  let S := p ^ (n - k - 1)
  let mut cur : Array (Array Nat) := #[]
  let mut tk : Array Nat := Array.emptyWithCapacity (p * S)
  for e in [0:p] do
    for r in [0:S] do
      if e + 1 < p then
        tk := tk.push ((e + 1) * S + r)
      else
        tk := tk.push (applyWord prev (k + 1) n pw[k]! r)
  cur := cur.push tk
  for t in [0:n - k - 1] do
    let j := k + 1 + t
    let mut tj : Array Nat := Array.emptyWithCapacity (p * S)
    let mut dv := unitVec n j
    for e in [0:p] do
      for r in [0:S] do
        tj := tj.push (e * S + applyWord prev (k + 1) n dv r)
      let mut idx := 0
      for s in [0:n - k - 1] do
        let m := n - 1 - s
        for _ in [0:dv[m]!] do
          idx := applyWord prev (k + 1) n cwR[k * n + m]! idx
      dv := digitsOf p n idx
    cur := cur.push tj
  return cur

@[expose] def levelTables (p n : Nat) (pw cwR : Array (Array Nat)) :
    Array (Array (Array Nat)) := Id.run do
  let mut levels : Array (Array (Array Nat)) := Array.replicate (n + 1) #[]
  for t in [0:n] do
    let k := n - 1 - t
    levels := levels.set! k (stepLevel p n k pw cwR levels[k + 1]!)
  return levels

@[expose] def leftTables (p n : Nat) (pw cwR : Array (Array Nat)) : Array (Array Nat) :=
  (levelTables p n pw cwR)[0]!

@[expose] def firstPos (p n i : Nat) : Nat :=
  let d := digitsOf p n i
  (List.range n).findIdx (fun k => d[k]! != 0)

@[expose] def parTree (p n : Nat) : Array (Nat × Nat) := Id.run do
  let mut a : Array (Nat × Nat) := Array.emptyWithCapacity (p ^ n)
  a := a.push (0, 0)
  for i in [1:p ^ n] do
    let j := firstPos p n i
    a := a.push (i - p ^ (n - 1 - j), j)
  return a

@[expose] def rangeOK (p n : Nat) (L : Array (Array Nat)) : Bool :=
  L.size == n && L.all fun T => T.size == p ^ n && parAll (p ^ n) 31 fun x => decide (T[x]! < p ^ n)

@[expose] def invTab (N : Nat) (T : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate N 0
  for x in [0:N] do
    r := r.set! T[x]! x
  return r

@[expose] def injOK (p n : Nat) (L : Array (Array Nat)) : Bool :=
  L.all fun T => (let R := invTab (p ^ n) T; parAll (p ^ n) 31 fun x => R[T[x]!]! == x)

@[expose] def edgeOK (p n : Nat) (L : Array (Array Nat)) (P : Array (Nat × Nat)) : Bool :=
  P.size == p ^ n && parAll (p ^ n) 31 fun i =>
    i == 0 || (decide ((P[i]!).1 < i) && decide ((P[i]!).2 < n) &&
      (L[(P[i]!).2]!)[(P[i]!).1]! == i)

@[expose] def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, y => y
  | k + 1, y => iterN f k (f y)

@[inline, expose] def stepAt (L : Array (Array Nat)) (m y : Nat) : Nat := (L[m]!)[y]!

@[expose] def wordAt (n : Nat) (L : Array (Array Nat)) (ds : Array Nat) (x : Nat) : Nat :=
  (List.range n).foldr (fun m y => iterN (stepAt L m) ds[m]! y) x

@[expose] def relOK (p n : Nat) (L : Array (Array Nat)) (pw cw : Array (Array Nat)) : Bool :=
  pw.size == n && cw.size == n * n &&
    (List.range n).all (fun i => parAll (p ^ n) 31 fun x =>
      iterN (stepAt L i) p x == wordAt n L pw[i]! x) &&
    (List.range n).all (fun i => (List.range n).all fun j => i >= j ||
      parAll (p ^ n) 31 fun x => (L[i]!)[(L[j]!)[x]!]! == wordAt n L cw[i * n + j]! ((L[i]!)[x]!))

@[expose] def suppOK (p n : Nat) (pw cw : Array (Array Nat)) : Bool :=
  (List.range n).all (fun i => (List.range n).all fun k =>
    pw[i]![k]! < p && (k > i || pw[i]![k]! == 0)) &&
    (List.range n).all fun i => (List.range n).all fun j => i >= j ||
      (List.range n).all fun k => cw[i * n + j]![k]! < p && (k > i || cw[i * n + j]![k]! == 0)

@[expose] def tabPowIdx (P : Array (Nat × Nat)) (L : Array (Array Nat)) (a : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tabMul P L a (tabPowIdx P L a k)

@[expose] def genInvIdx (n : Nat) (L : Array (Array Nat)) (N : Nat) : Array Nat :=
  (Array.range n).map fun j => ((List.range N).findIdx fun x => (L[j]!)[x]! == 0)

structure PcLab where
  lab : Array Nat
  wit : Array Nat
  rep : Array Nat

@[expose] def pcLabels (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (inv : Array Nat) : PcLab := Id.run do
  let N := p ^ n
  let mut lab : Array Nat := Array.replicate N N
  let mut wit : Array Nat := Array.replicate N 0
  let mut rep : Array Nat := #[]
  for i in [1:N] do
    if lab[i]! == N && tabPowIdx P L i p == 0 then
      let l := rep.size
      rep := rep.push i
      lab := lab.set! i l
      wit := wit.set! i 0
      let mut q : Array Nat := #[i]
      let mut h := 0
      for _ in [0:N] do
        if h < q.size then
          let u := q[h]!
          for j in [0:n] do
            let v := (L[j]!)[tabMul P L u inv[j]!]!
            if lab[v]! == N then
              lab := lab.set! v l
              wit := wit.set! v (tabMul P L wit[u]! inv[j]!)
              q := q.push v
          h := h + 1
        else
          break
  return { lab, wit, rep }

@[expose] def pcClassOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (lab wit rep : Array Nat) : Bool :=
  parAll (p ^ n) 63 fun i => i == 0 || tabPowIdx P L i p != 0 ||
    (decide (lab[i]! < rep.size) && decide (wit[i]! < p ^ n) && decide (rep[lab[i]!]! < p ^ n) &&
      tabMul P L wit[i]! i == tabMul P L rep[lab[i]!]! wit[i]!)

@[expose] def centerOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat)) : Bool :=
  decide (0 < n) && (List.range (p - 1)).all (fun i => (L[n - 1]!)[i]! == i + 1) &&
    parAll (p ^ n) 63 fun i => decide (i < p) || (List.range n).any fun j =>
      tabMul P L (L[j]!)[0]! i != tabMul P L i (L[j]!)[0]!

@[expose] def pcRegOK (p n : Nat) (pw cw cwR : Array (Array Nat)) : Bool :=
  let L := leftTables p n pw cwR
  let P := parTree p n
  rangeOK p n L && injOK p n L && edgeOK p n L P && suppOK p n pw cw && relOK p n L pw cw

@[expose] def pcLab (p n : Nat) (pw cwR : Array (Array Nat)) : PcLab :=
  pcLabels p n (parTree p n) (leftTables p n pw cwR)
    (genInvIdx n (leftTables p n pw cwR) (p ^ n))

@[expose] def pcFullOK (p n : Nat) (pw cw cwR : Array (Array Nat)) : Bool :=
  pcRegOK p n pw cw cwR && centerOK p n (parTree p n) (leftTables p n pw cwR) &&
    pcClassOK p n (parTree p n) (leftTables p n pw cwR) (pcLab p n pw cwR).lab
      (pcLab p n pw cwR).wit (pcLab p n pw cwR).rep

end Timmesfeld.PcReg
