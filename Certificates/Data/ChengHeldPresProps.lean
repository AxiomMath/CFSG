module

public import Certificates.Data.ChengHeldPres

public section

namespace CFSG.OddStandard.ChengHeldData

open CFSG.PSL3Four.Native

structure RegModel where
  N : ℕ
  mul : Array ℕ
  inv : Array ℕ
  gpt : Array ℕ
  order : Array ℕ
  parent : Array ℕ
  label : Array ℕ

@[noinline, expose] def mkReg (α : ℕ) : RegModel :=
  let E := regEnum α
  let N := regN α
  let T := E.tabs
  let pe : Array Tab := Id.run do
    let mut a : Array Tab := Array.replicate N (idTab N)
    for i in [0:T.size] do
      a := a.set! (T[i]!)[0]! T[i]!
    return a
  let mul : Array ℕ := Array.ofFn (n := N * N) fun k => (pe[k.val / N]!)[k.val % N]!
  let inv : Array ℕ := Array.ofFn (n := N) fun a =>
    ((List.range N).find? fun b => mul[a.val * N + b]! == 0).getD 0
  let gpt : Array ℕ := (regGens α).map fun g => g[0]!
  { N := N, mul := mul, inv := inv, gpt := gpt,
    order := T.map fun t => t[0]!, parent := E.par.map fun p => (T[p]!)[0]!, label := E.lab }

namespace RegModel

variable (M : RegModel)

@[inline, expose] def m (a b : ℕ) : ℕ := M.mul[a * M.N + b]!

@[expose] def pw (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => M.m (pw a n) a

@[expose] def ord (a : ℕ) : ℕ :=
  ((List.range (M.N + 1)).find? fun k => k > 0 && M.pw a k == 0).getD 0

@[expose] def cm (a b : ℕ) : ℕ := M.m (M.m (M.inv[a]!) (M.inv[b]!)) (M.m a b)

@[expose] def cj (a b : ℕ) : ℕ := M.m (M.m (M.inv[b]!) a) b

@[expose] def closure (gs : List ℕ) : Array Bool := Id.run do
  let mut mem : Array Bool := Array.replicate M.N false
  mem := mem.set! 0 true
  let mut queue : Array ℕ := #[0]
  let mut qi := 0
  while qi < queue.size do
    let x := queue[qi]!
    qi := qi + 1
    for g in gs do
      let y := M.m x g
      if !mem[y]! then
        mem := mem.set! y true
        queue := queue.push y
  return mem

@[expose] def elems (B : Array Bool) : List ℕ := (List.range B.size).filter fun i => B[i]!

@[expose] def card (B : Array Bool) : ℕ := (elems B).length

@[expose] def g (j : ℕ) : ℕ := M.gpt[j]!

@[expose] def bInter (A B : Array Bool) : Array Bool :=
  (Array.range A.size).map fun i => A[i]! && B[i]!

@[expose] def bUnion (A B : Array Bool) : Array Bool :=
  (Array.range A.size).map fun i => A[i]! || B[i]!

@[expose] def bSubset (A B : Array Bool) : Bool := (List.range A.size).all fun i => !A[i]! || B[i]!

@[expose] def center : Array Bool :=
  (Array.range M.N).map fun a => (List.range M.N).all fun b => M.m a b == M.m b a

@[expose] def cent (B : Array Bool) : Array Bool :=
  (Array.range M.N).map fun a => (elems B).all fun b => M.m a b == M.m b a

@[expose] def commSub (A B : Array Bool) : Array Bool :=
  let cs := (elems A).flatMap fun a => (elems B).map fun b => M.cm a b
  let bm := cs.foldl (fun (bm : Array Bool) c => bm.set! c true) (Array.replicate M.N false)
  M.closure (elems bm)

@[expose] def invols (B : Array Bool) : List ℕ := (elems B).filter fun a => a != 0 && M.m a a == 0

@[expose] def ord4 (B : Array Bool) : List ℕ := (elems B).filter fun a => M.ord a == 4

@[expose] def isAbelian (B : Array Bool) : Bool :=
  (elems B).all fun a => (elems B).all fun b => M.m a b == M.m b a

@[expose] def isElemAb (B : Array Bool) : Bool :=
  M.isAbelian B && (elems B).all fun a => M.m a a == 0

@[expose] def evalT : Tm → ℕ
  | .var i => M.g i
  | .one => 0
  | .mul a b => M.m (evalT a) (evalT b)
  | .inv a => M.inv[evalT a]!

@[expose] def tabImgs (α k : ℕ) : Array ℕ :=
  let rels := if α = 2 then act2Rels k else actRels α k
  (Array.range 7).map fun j => match rels.find? (fun e => e.1 == j) with
    | some e => M.evalT e.2
    | none => 0

@[expose] def autMap (img : Array ℕ) : Array ℕ := Id.run do
  let mut a : Array ℕ := Array.replicate M.N 0
  for i in [1:M.order.size] do
    let x := M.order[i]!
    a := a.set! x (M.m (img[M.label[i]!]!) (a[M.parent[i]!]!))
  return a

@[expose] def isInvolAut (a : Array ℕ) : Bool :=
  a.size == M.N && (List.range M.N).all (fun x => a[a[x]!]! == x) &&
    (List.range M.N).all fun x => (List.range M.N).all fun y =>
      a[M.m x y]! == M.m (a[x]!) (a[y]!)

@[expose] def fixedPts (a : Array ℕ) : Array Bool := (Array.range M.N).map fun x => a[x]! == x

@[expose] def twInvs (a : Array ℕ) : List ℕ := (List.range M.N).filter fun s => M.m s (a[s]!) == 0

@[expose] def twOrbits (a : Array ℕ) : List (List ℕ) := Id.run do
  let mut seen : Array Bool := Array.replicate M.N false
  let mut orbs : List (List ℕ) := []
  for s in M.twInvs a do
    if !seen[s]! then
      let orb := ((List.range M.N).map fun x => M.m (M.m (M.inv[x]!) s) (a[x]!)).eraseDups
      for y in orb do
        seen := seen.set! y true
      orbs := orbs ++ [orb]
  return orbs

@[expose] def gImgs (α : ℕ) : Array ℕ :=
  (Array.range 7).map fun j => match (gRels α).find? (fun e => e.1 == j) with
    | some e => M.evalT e.2
    | none => 0

@[expose] def isHom (a : Array ℕ) : Bool :=
  a.size == M.N && (List.range M.N).all fun x => (List.range M.N).all fun y =>
    a[M.m x y]! == M.m (a[x]!) (a[y]!)

@[expose] def isBij (a : Array ℕ) : Bool :=
  ((List.range M.N).foldl (fun (s : Array Bool) x => s.set! (a[x]!) true)
    (Array.replicate M.N false)).all id

@[expose] def permOrd (a : Array ℕ) : ℕ :=
  ((List.range 13).find? fun k => k > 0 &&
    (List.range M.N).all fun x => (List.range k).foldl (fun y _ => a[y]!) x == x).getD 0

@[expose] def conjArr (s : ℕ) : Array ℕ := (Array.range M.N).map fun x => M.cj x s

@[expose] def orbitOf (maps : List (Array ℕ)) (x : ℕ) : List ℕ := Id.run do
  let mut seen : Array Bool := Array.replicate M.N false
  seen := seen.set! x true
  let mut queue : Array ℕ := #[x]
  let mut qi := 0
  while qi < queue.size do
    let y := queue[qi]!
    qi := qi + 1
    for f in maps do
      let z := f[y]!
      if !seen[z]! then
        seen := seen.set! z true
        queue := queue.push z
  return queue.toList

@[expose] def eaMask (E : Array ℕ) : ℕ := E.foldl (fun m i => m ||| (1 <<< i)) 0

@[expose] def eaNext (invs : Array ℕ) (L : Array (Array ℕ)) : Array (Array ℕ) := Id.run do
  let mut seen : Std.HashSet ℕ := {}
  let mut out : Array (Array ℕ) := #[]
  for E in L do
    let m := eaMask E
    for a in invs do
      if !(m.testBit a) && E.all fun e => M.m a e == M.m e a then
        let E' := E ++ E.map fun e => M.m a e
        let m' := eaMask E'
        if !(seen.contains m') then
          seen := seen.insert m'
          out := out.push E'
  return out

@[expose] def eaCounts : List ℕ :=
  let invs := ((List.range M.N).filter fun a => a != 0 && M.m a a == 0).toArray
  let L1 := invs.map fun a => #[0, a]
  let L2 := M.eaNext invs L1
  let L3 := M.eaNext invs L2
  let L4 := M.eaNext invs L3
  let L5 := M.eaNext invs L4
  let L6 := M.eaNext invs L5
  [L1.size, L2.size, L3.size, L4.size, L5.size, L6.size]

end RegModel

open RegModel

@[expose] def struct4OK (α : ℕ) : Bool :=
  let M := mkReg α
  let t := M.g 0
  let pi := M.g 1
  let tau := M.g 2
  let mu := M.g 3
  let lam := M.g 4
  let ze := M.g 5
  let xi := M.g 6
  let Zt := M.closure [t]
  let D := M.closure [t, pi, tau]
  let R1 := M.closure [t, pi, tau, mu, lam]
  let R2 := M.closure [t, pi, tau, ze, xi]
  let V := M.closure [M.pw t 2, pi, M.m t tau]
  let W := M.cent V
  let mlx := M.m (M.m mu lam) xi
  M.N == 256 && M.ord t == 4 && M.center == Zt && card Zt == 4 &&
    M.commSub (Array.replicate M.N true) (Array.replicate M.N true) == D && card D == 16 &&
    card R1 == 64 && card R2 == 64 && bInter R1 R2 == D && bInter R1 (M.cent R1) == Zt &&
    bInter R2 (M.cent R2) == Zt &&
    (M.invols (Array.replicate M.N true)).length == 55 &&
    (M.invols (bUnion R1 R2)).length == 55 &&
    ((M.invols R1).filter fun a => !Zt[a]!).length == 30 &&
    ((M.ord4 R1).filter fun a => !Zt[a]!).length == 30 &&
    ((M.invols R2).filter fun a => !Zt[a]!).length == 30 &&
    ((M.ord4 R2).filter fun a => !Zt[a]!).length == 30 &&
    ((List.range M.N).filter fun s => M.pw s 2 == t || M.pw s 2 == M.inv[t]!).length == 0 &&
    M.eaCounts == [55, 143, 29, 0, 0, 0] &&
    M.isElemAb V && card V == 8 && card W == 64 &&
    M.isAbelian W == (α == 0) && ((M.invols W).all fun a => V[a]!) &&
    ((elems W).all fun a => M.ord a != 8) &&
    (α == 0 || (bInter W (M.cent W) == M.closure [t, pi, M.m t tau] &&
      M.commSub W W == M.closure [M.pw t 2])) &&
    (M.cm mlx (M.m (M.m mu ze) xi) == 0) == (α == 0) &&
    (M.pw (M.m mlx tau) 2 == pi)

@[expose] def struct2OK : Bool :=
  let M := mkReg 2
  let q := M.g 0
  let pi := M.g 1
  let tau := M.g 2
  let mu := M.g 3
  let lam := M.g 4
  let ze := M.g 5
  let xi := M.g 6
  let D := M.closure [q, pi, tau]
  let R1 := M.closure [q, pi, tau, mu, lam]
  let R2 := M.closure [q, pi, tau, ze, xi]
  let hasRoot := fun x => (List.range M.N).any fun s => M.pw s 2 == x
  M.N == 128 && M.ord q == 2 && M.center == D && card D == 8 &&
    M.commSub (Array.replicate M.N true) (Array.replicate M.N true) == D &&
    card R1 == 32 && card R2 == 32 && M.isElemAb R1 && M.isElemAb R2 && bInter R1 R2 == D &&
    (M.invols (Array.replicate M.N true)).length == 55 &&
    (M.invols (bUnion R1 R2)).length == 55 &&
    M.eaCounts == [55, 303, 309, 62, 2, 0] && !hasRoot q &&
    hasRoot pi && hasRoot (M.m q pi) && hasRoot tau && hasRoot (M.m q tau) &&
    M.pw (M.m (M.m mu lam) xi) 2 == pi && M.pw (M.m mu ze) 2 == M.m q pi

@[expose] def autData (α k : ℕ) : ℕ × ℕ × List ℕ × Bool :=
  if α = 0 then
    if k = 0 then (32, 16, [8, 8], false) else if k = 1 then (8, 64, [32, 32], true)
    else (8, 32, [32], true)
  else if α = 1 then
    if k = 0 then (16, 32, [16, 16], true) else if k = 1 then (16, 32, [16, 16], false)
    else (8, 32, [32], true)
  else
    if k = 0 then (16, 16, [8, 8], false) else if k = 1 then (8, 32, [16, 16], false)
    else (8, 16, [16], true)

@[expose] def autOK (α : ℕ) : Bool :=
  let M := mkReg α
  let q := if α = 2 then M.g 0 else M.pw (M.g 0) 2
  let t := M.g 0
  let pi := M.g 1
  let tau := M.g 2
  let mlx := M.m (M.m (M.g 3) (M.g 4)) (M.g 6)
  ([0, 1, 2].all fun k =>
    let a := M.autMap (M.tabImgs α k)
    let d := autData α k
    M.isInvolAut a && card (M.fixedPts a) == d.1 && (M.twInvs a).length == d.2.1 &&
      (M.twOrbits a).map List.length == d.2.2.1 &&
      ((M.twOrbits a).any fun o => o.contains 0 && o.contains q) == d.2.2.2) &&
  (let aF := M.autMap (M.tabImgs α 0)
   let aG := M.autMap (M.tabImgs α 1)
   let aU := M.autMap (M.tabImgs α 2)
   let cF := M.closure [t, pi, M.m (M.g 3) (M.g 4), M.g 6]
   let cG := M.closure [t, pi, tau]
   let cU := M.closure [t, M.m mlx tau]
   if α = 2 then
     M.fixedPts aF == cF && M.fixedPts aG == cG && M.fixedPts aU == cU &&
       (let orbG := (M.twOrbits aG).find? fun o => o.contains 0
        match orbG with
        | some o => o.contains pi && o.contains (M.m q tau) && o.contains (M.m q (M.m pi tau))
        | none => false)
   else
     bSubset (M.fixedPts aF) cF && bSubset (M.fixedPts aG) cG && bSubset (M.fixedPts aU) cU)

@[expose] def gAutOK (α : ℕ) : Bool :=
  let M := mkReg α
  let t := M.g 0
  let pi := M.g 1
  let tau := M.g 2
  let a := M.autMap (M.gImgs α)
  let Zt := M.closure [t]
  let D := M.closure [t, pi, tau]
  let maps := a :: (List.range 7).map fun j => M.conjArr (M.g j)
  M.isHom a && M.isBij a && M.permOrd a == 3 &&
    ((List.range M.N).filter fun x => Zt[M.m (M.inv[x]!) (a[x]!)]!).length == card Zt &&
    (elems D).all (fun x => D[a[x]!]!) &&
    (if α = 2 then
      let op := M.orbitOf maps pi
      let ot := M.orbitOf maps tau
      let q := t
      card D == 8 && (M.orbitOf maps q).length == 1 &&
        op.length == 3 && op.contains (M.m (M.m q pi) tau) && op.contains (M.m q tau) &&
        ot.length == 3 && ot.contains (M.m q pi) && ot.contains (M.m pi tau) &&
        ([pi, M.m (M.m q pi) tau, M.m q tau, tau, M.m q pi, M.m pi tau, q].eraseDups).length == 7
    else
      let q := M.pw t 2
      let V := M.closure [q, pi, M.m t tau]
      let op := M.orbitOf maps pi
      card V == 8 && (elems V).all (fun x => V[a[x]!]!) && op.length == 6 &&
        (elems V).all fun x => x == 0 || x == q || op.contains x)

@[noinline, expose] def chPropsOK : Bool :=
  struct4OK 0 && struct4OK 1 && struct2OK && autOK 0 && autOK 1 && autOK 2 &&
    gAutOK 0 && gAutOK 1 && gAutOK 2

end CFSG.OddStandard.ChengHeldData
