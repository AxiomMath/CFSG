module

public import Certificates.Data.Sp43.Code
public import Certificates.Data.Sp43.Data

public section

namespace CFSG.Sp43.Native

set_option compiler.extract_closed false

@[expose] def memS (L : Array Nat) (c : Nat) : Bool :=
  go 0 L.size (L.size + 1)
where
  go (lo hi : Nat) : Nat → Bool
    | 0 => false
    | f + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if L[mid]! == c then true
        else if L[mid]! < c then go (mid + 1) hi f else go lo mid f
      else false

@[expose] def posS (L : Array Nat) (c : Nat) : Nat :=
  go 0 L.size (L.size + 1)
where
  go (lo hi : Nat) : Nat → Nat
    | 0 => L.size
    | f + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if L[mid]! == c then mid
        else if L[mid]! < c then go (mid + 1) hi f else go lo mid f
      else L.size

@[expose] def bfs (gens : Array Nat) (cap : Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  Id.run do
    let mut E : Array Nat := #[oneC]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut dep : Array Nat := #[0]
    for h in [0:cap] do
      if h < E.size then
        for g in [0:gens.size] do
          let y := mulF E[h]! gens[g]!
          if !E.contains y then
            E := E.push y
            par := par.push h
            lab := lab.push g
            dep := dep.push (dep[h]! + 1)
    let perm := (Array.range E.size).qsort fun i j => E[i]! < E[j]!
    let inv := Id.run do
      let mut a := Array.replicate E.size 0
      for k in [0:perm.size] do
        a := a.set! perm[k]! k
      return a
    return (perm.map (E[·]!), perm.map fun i => inv[par[i]!]!, perm.map (lab[·]!),
      perm.map (dep[·]!))

@[expose] def incOK (L : Array Nat) : Bool :=
  (List.range (L.size - 1)).all fun i => L[i]! < L[i + 1]!

@[expose] def treeOK (L gens par lab dep : Array Nat) : Bool :=
  par.size == L.size && lab.size == L.size && dep.size == L.size &&
    (List.range L.size).all fun i =>
      (dep[i]! == 0 && L[i]! == oneC) ||
        (decide (par[i]! < L.size) && decide (lab[i]! < gens.size) &&
          decide (dep[par[i]!]! < dep[i]!) && L[i]! == mulF L[par[i]!]! gens[lab[i]!]!)

@[expose] def closedOK (L gens : Array Nat) : Bool :=
  memS L oneC && L.all fun y => gens.all fun g => memS L (mulF y g)

@[expose] def subOK (gens : Array Nat) (n : Nat)
    (r : Array Nat × Array Nat × Array Nat × Array Nat) : Bool :=
  r.1.size == n && incOK r.1 && treeOK r.1 gens r.2.1 r.2.2.1 r.2.2.2 && closedOK r.1 gens

@[expose] def cubeC (c : Nat) : Nat := mulF (mulF c c) c

@[expose] def pow9 (c : Nat) : Nat := cubeC (cubeC c)

@[expose] def spArr (_ : Unit := ()) : Array Nat := (spCodes ()).toArray

@[expose] def threeArr (E : Array Nat) : Array Nat :=
  E.filter fun c => c != oneC && pow9 c == oneC

@[expose] def etree (E gens : Array Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let n := E.size
  let mut par := Array.replicate n 0
  let mut lab := Array.replicate n 0
  let mut dep := Array.replicate n 0
  let r := posS E oneC
  let mut seen := (Array.replicate n false).set! r true
  let mut queue := #[r]
  for k in [0:n] do
    if k < queue.size then
      let t := queue[k]!
      for g in [0:gens.size] do
        let u := posS E (mulF E[t]! gens[g]!)
        if u < n && !seen[u]! then
          seen := seen.set! u true
          par := par.set! u t
          lab := lab.set! u g
          dep := dep.set! u (dep[t]! + 1)
          queue := queue.push u
  return (par, lab, dep)

@[expose] def conjC (n ni y : Nat) : Nat := mulF (mulF n y) ni

@[expose] def normOK (L : Array Nat) (gs : Nat × Nat) (ns nis : Nat × Nat) : Bool :=
  mulF ns.1 nis.1 == oneC && mulF ns.2 nis.2 == oneC &&
    #[gs.1, gs.2].all fun k => memS L (conjC ns.1 nis.1 k) && memS L (conjC ns.2 nis.2 k)

@[expose] def orbits (_L T : Array Nat) (ns nis : Nat × Nat) (reps : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let n := T.size
  let mut kind := Array.replicate n 0
  let mut par := Array.replicate n 0
  let mut lab := Array.replicate n 0
  let mut rep := Array.replicate n 0
  let mut dep := Array.replicate n 0
  let mut seen := Array.replicate n false
  let mut queue : Array Nat := #[]
  for r in [0:reps.size] do
    let t := posS T reps[r]!
    if t < n && !seen[t]! then
      seen := seen.set! t true
      kind := kind.set! t 1
      rep := rep.set! t r
      queue := queue.push t
  for k in [0:n] do
    if k < queue.size then
      let t := queue[k]!
      for l in [0:2] do
        let m := if l == 0 then ns.1 else ns.2
        let mi := if l == 0 then nis.1 else nis.2
        let u := posS T (conjC m mi T[t]!)
        if u < n && !seen[u]! then
          seen := seen.set! u true
          kind := kind.set! u 1
          par := par.set! u t
          lab := lab.set! u l
          rep := rep.set! u rep[t]!
          dep := dep.set! u (dep[t]! + 1)
          queue := queue.push u
  return (kind, par, lab, rep, dep)

@[expose] def orbitOK (L T : Array Nat) (ns nis : Nat × Nat) (reps : Array Nat)
    (w : Array Nat × Array Nat × Array Nat × Array Nat × Array Nat) : Bool :=
  let (kind, par, lab, rep, dep) := w
  kind.size == T.size && par.size == T.size && lab.size == T.size && rep.size == T.size &&
    dep.size == T.size &&
    (List.range T.size).all fun t =>
      (kind[t]! == 0 && memS L T[t]!) ||
        (kind[t]! == 1 && decide (rep[t]! < reps.size) &&
          ((dep[t]! == 0 && T[t]! == reps[rep[t]!]!) ||
            (decide (par[t]! < T.size) && kind[par[t]!]! == 1 && rep[par[t]!]! == rep[t]! &&
              decide (dep[par[t]!]! < dep[t]!) &&
              ((lab[t]! == 0 && T[t]! == conjC ns.1 nis.1 T[par[t]!]!) ||
                (lab[t]! == 1 && T[t]! == conjC ns.2 nis.2 T[par[t]!]!)))))

@[expose] def evalW (gl : Array Nat) (w : Word) : Nat :=
  w.foldl (fun acc ae => mulF acc (powC gl[ae.1]! ae.2)) oneC

@[expose] def caseOK (Ls : Array (Array Nat)) (gs : Nat × Nat) (c : Case) : Bool :=
  let gl := #[gs.1, gs.2, c.x]
  let h := memGens[c.j]!
  decide (c.j < 6) && mulF c.g c.gi == oneC &&
    c.w1.all (fun ae => decide (ae.1 < 3)) && c.w2.all (fun ae => decide (ae.1 < 3)) &&
    (c.j == 5 || gl.all fun k => memS Ls[c.j]! (conjC c.g c.gi k)) &&
    evalW gl c.w1 == conjC c.gi c.g h.1 && evalW gl c.w2 == conjC c.gi c.g h.2

@[expose] def negV (v : Nat) : Nat := horner ((List.range 4).map fun i => 2 * dig v i)

@[expose] def noEigOK (c : Nat) : Bool :=
  (List.range 80).all fun k => vecC c (k + 1) != k + 1 && vecC c (k + 1) != negV (k + 1)

@[expose] def h3OK (L : Array Nat) : Bool := memS L minusOneC

@[expose] def h4OK (L : Array Nat) : Bool :=
  let (p, u, v, ui, vi) := h4Data
  memS L p && p != oneC && cubeC p == oneC && memS L u && memS L v &&
    mulF u ui == oneC && mulF v vi == oneC &&
    (conjC u ui p == p || conjC u ui p == mulF p p) &&
    (conjC v vi p == p || conjC v vi p == mulF p p) &&
    subOK #[u, v] 48 (bfs #[u, v] 100)

@[expose] def gOK (E : Array Nat) : Bool :=
  let d := memGens[0]!.1
  let (p1, p2, b1, b2, b1i, b2i, e) := p0Data
  let d2 := mulF d d
  let ds := [d, d2, mulF d2 d, mulF d2 d2]
  let N0 := E.filter fun c => let cd := mulF c d; ds.any fun dk => cd == mulF dk c
  let P := bfs #[p1, p2] 100
  d != oneC && mulF (mulF d2 d2) d == oneC && N0.size == 40 &&
    N0.all (fun c => c == oneC || c == minusOneC || noEigOK c) &&
    subOK #[p1, p2] 81 P && P.1.all (fun y => pow9 y == oneC) &&
    ((List.range 81).filter fun v => vecC p1 v == v && vecC p2 v == v) == [0, e, negV e] &&
    mulF b1 b1i == oneC && mulF b2 b2i == oneC &&
    #[p1, p2].all (fun k => memS P.1 (conjC b1 b1i k) && memS P.1 (conjC b2 b2i k)) &&
    subOK #[b1, b2] 324 (bfs #[b1, b2] 400) &&
    subOK #[normGens[0]!.1, normGens[0]!.2] 40 (bfs #[normGens[0]!.1, normGens[0]!.2] 100)

@[expose] def memOrders : Array Nat := #[5, 120, 120, 720, 1920]

@[expose] def memberOK (T : Array Nat) (Ls : Array (Array Nat)) (i : Nat)
    (r : Array Nat × Array Nat × Array Nat × Array Nat) : Bool :=
  let gs := memGens[i]!
  let reps := cases[i]!.map (·.x)
  subOK #[gs.1, gs.2] memOrders[i]! r && normOK r.1 gs normGens[i]! normInvs[i]! &&
    orbitOK r.1 T normGens[i]! normInvs[i]! reps (orbits r.1 T normGens[i]! normInvs[i]! reps) &&
    cases[i]!.all (caseOK Ls gs)

@[expose] def membersOK (T : Array Nat)
    (R : Array (Array Nat × Array Nat × Array Nat × Array Nat)) : Bool :=
  let Ls := R.map (·.1)
  R.size == 5 && (List.range 5).all (fun i => memberOK T Ls i R[i]!) && h3OK Ls[3]! &&
    h4OK Ls[4]!

@[expose] def codesOK (E : Array Nat) : Bool :=
  let (p, u, v, ui, vi) := h4Data
  let (p1, p2, b1, b2, b1i, b2i, _) := p0Data
  memGens.all (fun g => memS E g.1 && memS E g.2) &&
    normGens.all (fun g => memS E g.1 && memS E g.2) &&
    normInvs.all (fun g => memS E g.1 && memS E g.2) &&
    cases.all (fun cs => cs.all fun c => memS E c.x && memS E c.g && memS E c.gi) &&
    [p, u, v, ui, vi, p1, p2, b1, b2, b1i, b2i, minusOneC].all (memS E)

@[expose] def groupOK (E : Array Nat) (tr : Array Nat × Array Nat × Array Nat) : Bool :=
  let gs := #[memGens[5]!.1, memGens[5]!.2]
  E.size == 51840 && incOK E && codesOK E && treeOK E gs tr.1 tr.2.1 tr.2.2 && gOK E

@[expose] def checkE (E : Array Nat) : Bool :=
  groupOK E (etree E #[memGens[5]!.1, memGens[5]!.2]) &&
    membersOK (threeArr E) ((Array.range 5).map fun i => bfs #[memGens[i]!.1, memGens[i]!.2] 2000)

@[expose] def sp43Check (_ : Unit := ()) : Bool := checkE (spArr ())

end CFSG.Sp43.Native

end
