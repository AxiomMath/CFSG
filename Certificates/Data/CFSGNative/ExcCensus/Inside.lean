module

public import Certificates.Data.CFSGNative.ExcCensus.Check
public import Std.Data.HashMap

public section

open Std

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

set_option compiler.extract_closed false

@[expose] def imgN (T : Tabs) (r u c : Nat) : Nat :=
  Nat.fold r (fun t _ acc => if c.testBit t then acc ||| 1 <<< T.rt[u]![t]! else acc) 0

@[expose] def closN (T : Tabs) (d r c : Nat) : Nat :=
  Nat.fold (3 ^ d) (fun v _ acc => if subN c T.zm[v]! then acc &&& T.zm[v]! else acc) (2 ^ r - 1)

@[expose] def growC (T : Tabs) (d r c : Nat) : Nat :=
  Nat.repeat (growN T r (closN T d r c)) r c

structure SatW where
  b : Array Nat
  e : Int
  n : Array (Array Int)
  k : Array Nat
  B : Array (Array Int)
  deriving Inhabited

structure A8W where
  b : Array Nat
  span : Array (Nat × Nat × Bool)
  cz : Nat
  hyp : Array (Nat × List (Nat × Nat))
  deriving Inhabited

structure ISearch where
  gens : Array Nat
  codes : Array Nat
  nreps : Nat
  parent : Array (Nat × Nat)
  img : Array (Array Nat)
  seed : Array Nat
  grow : Array (Array Nat)
  D : Nat
  Q : Array (Array Int)
  P : Array (Array Int)
  sat : Nat → Option SatW
  a8 : Nat → Option A8W
  deriving Inhabited

@[expose] def gensOK (T : Tabs) (r : Nat) (gens : Array Nat) : Bool :=
  Nat.all gens.size fun g _ =>
    let u := gens[g]!
    decide (u < r) && (Nat.all r fun t _ => T.rt[u]![T.rt[u]![t]!]! == t) &&
      Nat.all r fun i _ => Nat.all r fun j _ =>
        (T.adj[T.rt[u]![i]!]!).testBit T.rt[u]![j]! == (T.adj[i]!).testBit j

@[expose] def listOK (T : Tabs) (r : Nat) (X : ISearch) : Bool :=
  let n := X.codes.size
  (Nat.all n fun x _ => decide (X.codes[x]! < 2 ^ r)) &&
    (Nat.all n fun x _ => decide (x < X.nreps) ||
      (let p := X.parent[x]!
       decide (p.1 < x) && decide (p.2 < X.gens.size) &&
         imgN T r X.gens[p.2]! X.codes[p.1]! == X.codes[x]!)) &&
    Nat.all n fun x _ => Nat.all X.gens.size fun g _ =>
      decide (X.img[x]![g]! < n) && X.codes[X.img[x]![g]!]! == imgN T r X.gens[g]! X.codes[x]!

@[expose] def growOK (T : Tabs) (d r : Nat) (X : ISearch) : Bool :=
  let n := X.codes.size
  (Nat.all r fun i _ =>
    decide (X.seed[i]! < n) && X.codes[X.seed[i]!]! == growC T d r (1 <<< i)) &&
    Nat.all X.nreps fun x _ => Nat.all r fun j _ =>
      let c := X.codes[x]!
      c.testBit j || T.adj[j]! &&& c == 0 ||
        (decide (X.grow[x]![j]! < n) && X.codes[X.grow[x]![j]!]! == growC T d r (c ||| 1 <<< j))

@[expose] def factorOK (T : Tabs) (r D : Nat) (Q P : Array (Array Int)) : Bool :=
  Nat.all r fun i _ => Nat.all r fun j _ =>
    T.pair[i]![j]! == Nat.fold D (fun k _ s => s + Q[i]![k]! * P[j]![k]!) 0

@[expose] def satOK (T : Tabs) (r D : Nat) (P : Array (Array Int)) (c : Nat) (w : SatW) : Bool :=
  let ρ := w.b.size
  (Nat.all ρ fun a _ => decide (w.b[a]! < r) && c.testBit w.b[a]!) && w.e % 3 != 0 &&
    (Nat.all r fun i _ => !c.testBit i || Nat.all D fun kk _ =>
      w.e * P[i]![kk]! == Nat.fold ρ (fun a _ s => s + w.n[i]![a]! * P[w.b[a]!]![kk]!) 0) &&
    (Nat.all ρ fun a _ => decide (w.k[a]! < r)) &&
    invOK ρ (fun a a' => T.pair[w.k[a]!]![w.b[a']!]!) w.B

@[expose] def chainGramN (a a' : Nat) : Int :=
  if a = a' then 2 else if a + 1 = a' ∨ a' + 1 = a then -1 else 0

@[expose] def chainSumN (Q : Array (Array Int)) (b : Array Nat) (a a' k : Nat) : Int :=
  Nat.fold 8 (fun s _ acc => if a ≤ s ∧ s < a' then acc + Q[b[s]!]![k]! else acc) 0

@[expose] def chainExpN (T : Tabs) (b : Array Nat) (t : Nat) : Int :=
  Nat.fold 8 (fun a _ acc => acc + ((a + 1 : Nat) : Int) * T.pair[t]![b[a]!]!) 0

@[expose] def a8OK (T : Tabs) (d r D : Nat) (Q : Array (Array Int)) (c : Nat) (w : A8W) : Bool :=
  (Nat.all 8 fun a _ => decide (w.b[a]! < r) && c.testBit w.b[a]!) &&
    (Nat.all 8 fun a _ => Nat.all 8 fun a' _ =>
      T.pair[w.b[a]!]![w.b[a']!]! == chainGramN a a') &&
    (Nat.all r fun i _ => !c.testBit i ||
      (let e := w.span[i]!
       decide (e.1 < e.2.1) && decide (e.2.1 ≤ 8) && Nat.all D fun kk _ =>
         Q[i]![kk]! == (if e.2.2 then -1 else 1) * chainSumN Q w.b e.1 e.2.1 kk)) &&
    decide (w.cz < 3 ^ d) &&
    (Nat.all r fun t _ =>
      chainExpN T w.b t % 3 == 0 && chainExpN T w.b t / 3 % 3 == evA T d t w.cz) &&
    Nat.all d fun k _ =>
      let h := w.hyp[k]!
      decide (h.1 < 3) && inOK T d r c h.2 (combN d (3 ^ k) w.cz 1 (3 - h.1))

@[expose] def orthMaskN (T : Tabs) (r k : Nat) : Nat :=
  maskN r fun i => T.pair[k]![i]! == 0 && T.pair[i]![k]! == 0

@[expose] def flagE6N (T : Tabs) (r c : Nat) : Bool :=
  trunc r c == 2 ^ r - 1 || Nat.any r fun k _ => trunc r c == orthMaskN T r k

@[expose] def flagN (T : Tabs) (m : Fin 6) (X : ISearch) (c : Nat) : Bool :=
  if m.val = 2 ∨ m.val = 3 then flagE6N T (nroots m) c
  else if m.val = 5 then
    match X.a8 c with
    | some w => a8OK T (dim m) (nroots m) X.D X.Q c w
    | none => false
  else false

@[expose] def codeOK (T : Tabs) (m : Fin 6) (X : ISearch) (c : Nat) : Bool :=
  (match X.sat c with
    | some w => satOK T (nroots m) X.D X.P c w
    | none => false) || flagN T m X c

@[expose] def insideOK (m : Fin 6) (T : Tabs) (X : ISearch) : Bool :=
  let d := dim m
  let r := nroots m
  tabsOK m T && gensOK T r X.gens && listOK T r X && growOK T d r X &&
    factorOK T r X.D X.Q X.P && Nat.all X.codes.size fun x _ => codeOK T m X X.codes[x]!

def orbitS (T : Tabs) (r : Nat) (gens : Array Nat) (ix : HashMap Nat (Nat × Nat)) (o c : Nat) :
    Array Nat × Array (Nat × Nat) × Array (Array Nat) × HashMap Nat (Nat × Nat) := Id.run do
  let mut orb : Array Nat := #[c]
  let mut par : Array (Nat × Nat) := #[(0, 0)]
  let mut im : Array (Array Nat) := #[]
  let mut ix := ix.insert c (o, 0)
  let mut k := 0
  while k < orb.size do
    let x := orb[k]!
    let mut row : Array Nat := #[]
    for g in [0:gens.size] do
      let y := imgN T r gens[g]! x
      match ix[y]? with
      | some op => row := row.push op.2
      | none =>
        row := row.push orb.size
        ix := ix.insert y (o, orb.size)
        orb := orb.push y
        par := par.push (k, g)
    im := im.push row
    k := k + 1
  return (orb, par, im, ix)

def orbitsS (T : Tabs) (d r : Nat) (gens : Array Nat) :
    Array (Array Nat) × Array (Array (Nat × Nat)) × Array (Array (Array Nat)) ×
      HashMap Nat (Nat × Nat) × Array Nat × Array (Array Nat) := Id.run do
  let mut ix : HashMap Nat (Nat × Nat) := {}
  let mut orbs : Array (Array Nat) := #[]
  let mut pars : Array (Array (Nat × Nat)) := #[]
  let mut ims : Array (Array (Array Nat)) := #[]
  let mut seedM : Array Nat := #[]
  for i in [0:r] do
    let c := growC T d r (1 <<< i)
    seedM := seedM.push c
    if !ix.contains c then
      let (orb, par, im, ix') := orbitS T r gens ix orbs.size c
      ix := ix'
      orbs := orbs.push orb
      pars := pars.push par
      ims := ims.push im
  let mut growM : Array (Array Nat) := #[]
  let mut q := 0
  while q < orbs.size do
    let rep := orbs[q]![0]!
    let mut gm : Array Nat := Array.replicate r 0
    for j in [0:r] do
      if !rep.testBit j && T.adj[j]! &&& rep != 0 then
        let c := growC T d r (rep ||| 1 <<< j)
        gm := gm.set! j c
        if !ix.contains c then
          let (orb, par, im, ix') := orbitS T r gens ix orbs.size c
          ix := ix'
          orbs := orbs.push orb
          pars := pars.push par
          ims := ims.push im
    growM := growM.push gm
    q := q + 1
  return (orbs, pars, ims, ix, seedM, growM)

def listS (T : Tabs) (d r : Nat) (gens : Array Nat) :
    Array Nat × Nat × Array (Nat × Nat) × Array (Array Nat) × Array Nat × Array (Array Nat) :=
  Id.run do
  let (orbs, pars, ims, ix, seedM, growM) := orbitsS T d r gens
  let nreps := orbs.size
  let mut offs : Array Nat := #[]
  let mut acc := nreps
  for o in [0:nreps] do
    offs := offs.push acc
    acc := acc + (orbs[o]!.size - 1)
  let fin (o p : Nat) : Nat := if p == 0 then o else offs[o]! + p - 1
  let look (c : Nat) : Nat := match ix[c]? with
    | some op => fin op.1 op.2
    | none => 0
  let mut codes : Array Nat := #[]
  let mut parent : Array (Nat × Nat) := #[]
  let mut img : Array (Array Nat) := #[]
  for o in [0:nreps] do
    codes := codes.push orbs[o]![0]!
    parent := parent.push (0, 0)
    img := img.push ((ims[o]![0]!).map fun p => fin o p)
  for o in [0:nreps] do
    let orb := orbs[o]!
    for p in [1:orb.size] do
      codes := codes.push orb[p]!
      parent := parent.push (fin o (pars[o]![p]!).1, (pars[o]![p]!).2)
      img := img.push ((ims[o]![p]!).map fun p' => fin o p')
  return (codes, nreps, parent, img, seedM.map look, growM.map fun gm => gm.map look)

def greedyS (rows : Nat → Array Nat) (ids : List Nat) (nc lim : Nat) :
    Array Nat × Array Nat := Id.run do
  let mut ech : Array (Nat × Array Nat) := #[]
  let mut chosen : Array Nat := #[]
  for i in ids do
    if chosen.size < lim then
      let mut v := (Array.range nc).map fun t => (rows i)[t]! % 3
      for (pc, row) in ech do
        let f := v[pc]!
        if f != 0 then
          v := (Array.range nc).map fun t => (v[t]! + 9 - f * row[t]!) % 3
      match (List.range nc).find? (fun t => v[t]! != 0) with
      | none => pure ()
      | some pc =>
        let inv := if v[pc]! == 1 then 1 else 2
        let row := v.map fun x => x * inv % 3
        ech := ech.map fun (q, rw) =>
          let g := rw[pc]!
          (q, (Array.range nc).map fun t => (rw[t]! + 9 - g * row[t]!) % 3)
        ech := ech.push (pc, row)
        chosen := chosen.push i
  return (chosen, ech.map (·.1))

def bareissS (M : Array (Array Int)) (n : Nat) : Option (Array (Array Int) × Int) := Id.run do
  let mut A : Array (Array Int) := (Array.range n).map fun i =>
    (Array.range (2 * n)).map fun j => if j < n then M[i]![j]! else if j - n == i then 1 else 0
  let mut prev : Int := 1
  for k in [0:n] do
    let mut q : Option Nat := none
    for i in [k:n] do
      if q.isNone && A[i]![k]! != 0 then q := some i
    match q with
    | none => return none
    | some p =>
      if p != k then
        let rk := A[k]!
        A := (A.set! k A[p]!).set! p rk
      let akk := A[k]![k]!
      let rowk := A[k]!
      for i in [0:n] do
        if i != k then
          let rowi := A[i]!
          let aik := rowi[k]!
          A := A.set! i ((Array.range (2 * n)).map fun j =>
            (akk * rowi[j]! - aik * rowk[j]!) / prev)
      prev := akk
  return some ((Array.range n).map fun i => (A[i]!).extract n (2 * n), A[0]![0]!)

def satS (T : Tabs) (r D : Nat) (P : Array (Array Int)) (gens : Array Nat) (c : Nat) :
    Option SatW :=
  let (b, cols) := greedyS (fun i => (P[i]!).map m3) (bitsS r c).toList D D
  let ρ := b.size
  match bareissS (b.map fun i => cols.map fun col => P[i]![col]!) ρ with
  | none => none
  | some (E, e) =>
    let n := (Array.range r).map fun i =>
      if c.testBit i then
        (Array.range ρ).map fun a =>
          Nat.fold ρ (fun a2 _ s => s + P[i]![cols[a2]!]! * E[a2]![a]!) 0
      else #[]
    let (k, _) := greedyS (fun kk => b.map fun ba => m3 T.pair[kk]![ba]!)
      (gens.toList ++ List.range r) ρ ρ
    match inv3 (k.map fun ka => b.map fun ba => T.pair[ka]![ba]!) ρ with
    | none => none
    | some B => some { b, e, n, k, B }

def solveS (rows : Array (Array Nat)) (rhs : Array Nat) (nc : Nat) : Option (Array Nat) :=
  let (R, piv) := rref3 ((Array.range rows.size).map fun i => (rows[i]!).push rhs[i]!) (nc + 1)
  if piv.contains nc then none
  else some ((Array.range piv.size).foldl (fun x i => x.set! piv[i]! R[i]![nc]!)
    (Array.replicate nc 0))

def a8S (T : Tabs) (m : Fin 6) (ix : HashMap (Array Int) Nat) (d r D : Nat)
    (Q : Array (Array Int)) (gens : Array Nat) (c : Nat) : Option A8W := Id.run do
  let ss := simpleS m ix r c
  if ss.length != 8 then return none
  let nb (i : Nat) : List Nat := ss.filter fun j => j != i && T.pair[i]![j]! != 0
  let some e0 := ss.find? (fun i => (nb i).length == 1) | return none
  let mut b : Array Nat := #[e0]
  let mut prev := e0
  let mut cur := e0
  for _ in [0:7] do
    match (nb cur).find? (fun j => j != prev) with
    | some j =>
      prev := cur
      cur := j
      b := b.push j
    | none => pure ()
  let ivs := (List.range 9).flatMap fun a => ((List.range 9).filter (a < ·)).map fun a' =>
    ((a, a'), (Array.range D).map fun kk => chainSumN Q b a a' kk)
  let span := (Array.range r).map fun i =>
    if !c.testBit i then (0, 0, false) else
      let qi := (Array.range D).map fun kk => Q[i]![kk]!
      match ivs.find? (fun e => e.2 == qi) with
      | some e => (e.1.1, e.1.2, false)
      | none =>
        match ivs.find? (fun e => e.2 == qi.map (- ·)) with
        | some e => (e.1.1, e.1.2, true)
        | none => (0, 0, false)
  let some czv := solveS (gens.map fun g => (T.f[g]!).map m3)
    (gens.map fun g => m3 (chainExpN T b g / 3)) d | return none
  let cz := codeS czv
  let hyp := (Array.range d).map fun k =>
    ((List.range 3).findSome? fun x =>
      (insS T d r c (combN d (3 ^ k) cz 1 (3 - x))).map fun coef => (x, coef)).getD (0, [])
  return some { b, span, cz, hyp }

def iSearchOf (m : Fin 6) (T : Tabs) : ISearch :=
  let d := dim m
  let r := nroots m
  let ix := rootIdx m
  let gens := (simpleS m ix r (2 ^ r - 1)).toArray
  let (codes, nreps, parent, img, seed, grow) := listS T d r gens
  let m' : Fin 6 := if m.val = 3 then 2 else m
  let D := dim m'
  let Q := (Array.range r).map fun i => (Array.range D).map fun k => fN m' i k
  let P := (Array.range r).map fun i => (Array.range D).map fun k => hN m' i k
  { gens, codes, nreps, parent, img, seed, grow, D, Q, P,
    sat := satS T r D P gens
    a8 := if m.val = 5 then a8S T m ix d r D Q gens else fun _ => none }

@[expose] def insideCheck (m : Fin 6) : Bool :=
  let T := tabsOf m
  insideOK m T (iSearchOf m T)

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
