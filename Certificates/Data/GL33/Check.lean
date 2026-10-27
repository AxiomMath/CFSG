module

public import Certificates.Data.GL33.Code
public import Certificates.Data.GL33.Data

public section

namespace CFSG.GL33.Native

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
    let mut seen : Array Bool := (Array.replicate 19683 false).set! oneC true
    for h in [0:cap] do
      if h < E.size then
        for g in [0:gens.size] do
          let y := mulF E[h]! gens[g]!
          if !seen[y]! then
            seen := seen.set! y true
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

@[expose] def pow27 (c : Nat) : Nat := cubeC (cubeC (cubeC c))

@[expose] def glArr (_ : Unit := ()) : Array Nat := (glCodes ()).toArray

@[expose] def threeArr (E : Array Nat) : Array Nat :=
  E.filter fun c => c != oneC && pow27 c == oneC

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
  decide (c.j < 13) && mulF c.g c.gi == oneC &&
    c.w1.all (fun ae => decide (ae.1 < 3)) && c.w2.all (fun ae => decide (ae.1 < 3)) &&
    gl.all (fun k => memS Ls[c.j]! (conjC c.g c.gi k)) &&
    evalW gl c.w1 == conjC c.gi c.g h.1 && evalW gl c.w2 == conjC c.gi c.g h.2

@[expose] def kindOK (i : Nat) : Bool :=
  let gs := memGens[i]!
  let v := memVec[i]!
  if memKind[i]! == 0 then gs.1 == oneC && gs.2 == oneC
  else if memKind[i]! == 1 then
    v != 0 && decide (v < 27) && vecC gs.1 v == v && vecC gs.2 v == v
  else if memKind[i]! == 2 then
    v != 0 && decide (v < 27) && covC v gs.1 == v && covC v gs.2 == v
  else true

@[expose] def kindsOK : Bool :=
  memKind.size == 13 && memVec.size == 13 &&
    memKind == #[0, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5] && (List.range 13).all kindOK

@[expose] def normBy (L : Array Nat) (gs : Nat × Nat) (c : Nat) : Bool :=
  #[gs.1, gs.2].all fun a => L.any fun b => mulF c a == mulF b c

@[expose] def monoC (c : Nat) : Bool :=
  (List.range 3).all fun j => ((List.range 3).filter fun i => ent c i j != 0).length == 1

@[expose] def a4OK (E A : Array Nat) (mon : Array Nat × Array Nat × Array Nat × Array Nat) :
    Bool :=
  subOK #[monGens.1, monGens.2] 48 mon && mon.1.all monoC &&
    E.all fun c => !(normBy A memGens[6]! c) || memS mon.1 c

@[expose] def c13OK (E L : Array Nat) (ups : List Nat) : Bool :=
  memS L u13 && u13 != oneC && powC u13 13 == oneC &&
    ups == (List.range 12).map (fun k => powC u13 (k + 1)) &&
    E.all fun c => !(normBy L memGens[9]! c) || ups.any fun b => mulF c u13 == mulF b c

@[expose] def sylOK (E : Array Nat) (T : Array Nat × Array Nat × Array Nat × Array Nat) : Bool :=
  subOK #[sylGens.1, sylGens.2] 16 T && memS E minusOneC && T.1.all (· != minusOneC) &&
    (vecC sylGens.1 9 == 9 || vecC sylGens.1 9 == 18) &&
    (vecC sylGens.2 9 == 9 || vecC sylGens.2 9 == 18)

@[expose] def slOK : Bool := detC memGens[12]!.1 == 1 && detC memGens[12]!.2 == 1

@[expose] def memOrders : Array Nat := #[1, 3, 3, 9, 9, 9, 12, 24, 27, 39, 216, 216, 5616]

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
  R.size == 13 && memGens.size == 13 && cases.size == 13 &&
    (List.range 13).all fun i => memberOK T Ls i R[i]!

@[expose] def codesOK (E : Array Nat) : Bool :=
  memGens.all (fun g => memS E g.1 && memS E g.2) &&
    normGens.all (fun g => memS E g.1 && memS E g.2) &&
    normInvs.all (fun g => memS E g.1 && memS E g.2) &&
    cases.all (fun cs => cs.all fun c => memS E c.x && memS E c.g && memS E c.gi) &&
    [monGens.1, monGens.2, sylGens.1, sylGens.2, u13, minusOneC].all (memS E)

@[expose] def groupOK (E : Array Nat) : Bool := E.size == 11232 && incOK E && codesOK E

@[expose] def checkM (E : Array Nat) (R : Array (Array Nat × Array Nat × Array Nat × Array Nat))
    (mon T : Array Nat × Array Nat × Array Nat × Array Nat) (ups : List Nat) : Bool :=
  groupOK E && membersOK (threeArr E) R && kindsOK && slOK && a4OK E (R.map (·.1))[6]! mon &&
    c13OK E (R.map (·.1))[9]! ups && sylOK E T

@[expose] def gl33Check (_ : Unit := ()) : Bool :=
  checkM (glArr ()) ((Array.range 13).map fun i => bfs #[memGens[i]!.1, memGens[i]!.2] 6000)
    (bfs #[monGens.1, monGens.2] 100) (bfs #[sylGens.1, sylGens.2] 100)
    ((List.range 12).map fun k => powC u13 (k + 1))

end CFSG.GL33.Native

end
