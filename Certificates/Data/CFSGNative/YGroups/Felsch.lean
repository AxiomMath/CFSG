module

public import Std.Data.HashMap

public section

namespace CFSG.YGroups.Native

set_option compiler.extract_closed false

structure Fact where
  fx : Nat
  fc : Nat
  fy : Nat
  kind : Nat
  wi : Nat
  fs : Nat
  ft : Nat
  fo : Nat
  deriving Inhabited

structure Cert where
  N : Nat
  L : Nat
  pl : Array Nat
  facts : Array Fact
  refs : Array Nat
  rels : Array (List Nat)
  subs : Array (List Nat)
  live : Array Bool
  ffi : Array Nat
  ok : Bool
  deriving Inhabited

structure St where
  L : Nat
  inv : Array Nat
  rels : Array (List Nat)
  relIdx : Std.HashMap (List Nat) Nat
  rots : Array (Array Nat)
  subs : Array (List Nat)
  pl : Array Nat
  tab : Array Nat
  par : Array Nat
  lref : Array Nat
  facts : Array Fact
  refs : Array Nat
  cq : Array (Nat × Nat × Nat)
  ds : Array (Nat × Nat)
  ncoinc : Nat
  fail : Bool

namespace St

@[inline] def shift (_ : Unit := ()) : Nat := 2 ^ 33

@[inline] def enc (q r : Nat) : Nat := (q + 1) * shift + r

@[inline] def entry (s : St) (p c : Nat) : Option (Nat × Nat) :=
  let e := s.tab[p * s.L + c]!
  if e == 0 then none else some (e / shift - 1, e % shift)

@[inline] def setTab (s : St) (k v : Nat) : St :=
  let t := s.tab
  let s := { s with tab := #[] }
  { s with tab := t.set! k v }

@[inline] def setPar (s : St) (k v : Nat) : St :=
  let t := s.par
  let s := { s with par := #[] }
  { s with par := t.set! k v }

@[inline] def setLref (s : St) (k v : Nat) : St :=
  let t := s.lref
  let s := { s with lref := #[] }
  { s with lref := t.set! k v }

@[inline] def pushDs (s : St) (x : Nat × Nat) : St :=
  let t := s.ds
  let s := { s with ds := #[] }
  { s with ds := t.push x }

@[inline] def pushCq (s : St) (x : Nat × Nat × Nat) : St :=
  let t := s.cq
  let s := { s with cq := #[] }
  { s with cq := t.push x }

def wid (s : St) (w : List Nat) : St × Nat :=
  match s.relIdx.get? w with
  | some i => (s, i)
  | none =>
    let i := s.rels.size
    let r := s.rels
    let m := s.relIdx
    let s := { s with rels := #[], relIdx := {} }
    ({ s with rels := r.push w, relIdx := m.insert w i }, i)

def fact (s : St) (fx fc fy kind wi fs ft : Nat) (rs : Array Nat) : St × Nat :=
  let f := s.facts.size
  let fo := s.refs.size
  let F := s.facts
  let R := s.refs
  let s := { s with facts := #[], refs := #[] }
  ({ s with facts := F.push ⟨fx, fc, fy, kind, wi, fs, ft, fo⟩, refs := R ++ rs }, f)

@[inline] def rd (s : St) (r : Nat) : Nat × Nat × Nat :=
  let g := s.facts[r / 2]!
  if r % 2 == 0 then (g.fx, g.fc, g.fy) else (g.fy, s.inv[g.fc]!, g.fx)

@[inline] def alive (s : St) (p : Nat) : Bool := s.par[p]! == p

def newPoint (s : St) (p c : Nat) : St × Nat :=
  let q := s.pl.size
  let pl := s.pl
  let tab := s.tab
  let par := s.par
  let lref := s.lref
  let s := { s with pl := #[], tab := #[], par := #[], lref := #[] }
  let s := { s with pl := pl.push (p * (s.L + 1) + c),
                    tab := tab ++ Array.replicate s.L 0,
                    par := par.push q, lref := lref.push 0 }
  let (s, f) := s.fact p c q 0 0 0 0 #[]
  let s := s.setTab (p * s.L + c) (enc q (2 * f))
  let s := s.setTab (q * s.L + s.inv[c]!) (enc p (2 * f + 1))
  (s.pushDs (p, c), q)

def put (s : St) (p c q ref : Nat) : St :=
  let ci := s.inv[c]!
  match s.entry p c, s.entry q ci with
  | none, none =>
    let s := s.setTab (p * s.L + c) (enc q ref)
    let s := s.setTab (q * s.L + ci) (enc p (ref ^^^ 1))
    s.pushDs (p, c)
  | some (e1, r1), _ =>
    if e1 == q then s else
    let (s, w) := s.wid [ci, c, s.L]
    let (s, f) := s.fact e1 s.L q 2 w q 2 #[ref ^^^ 1, r1, 0]
    s.pushCq (e1, q, 2 * f)
  | none, some (e2, r2) =>
    let (s, w) := s.wid [c, ci, s.L]
    let (s, f) := s.fact e2 s.L p 2 w p 2 #[ref, r2, 0]
    s.pushCq (e2, p, 2 * f)

def toRep (s : St) (x : Nat) (fuel : Nat := 1000000) : St × Nat × Option Nat := Id.run do
  let mut chain : Array Nat := #[]
  let mut y := x
  for _ in [0:fuel] do
    if s.par[y]! == y then break
    chain := chain.push s.lref[y]!
    y := s.par[y]!
  if chain.size == 0 then return (s, y, none)
  if chain.size == 1 then return (s, y, some chain[0]!)
  let n := chain.size
  let (s, w) := s.wid (List.replicate (n + 1) s.L)
  let (s, f) := s.fact y s.L x 2 w x n (chain.push 0)
  let s := s.setPar x y
  let s := s.setLref x (2 * f + 1)
  return (s, y, some (2 * f + 1))

def mergeOne (s : St) (a b lam : Nat) : St := Id.run do
  let (s, ra, ar) := s.toRep a
  let (s, rb, br) := s.toRep b
  if ra == rb then return s
  let mut seq : Array Nat := #[]
  if let some r := ar then seq := seq.push (r ^^^ 1)
  seq := seq.push lam
  if let some r := br then seq := seq.push r
  let n := seq.size
  let mut s := s
  let mut rab := lam
  if n > 1 then
    let (s1, w) := s.wid (List.replicate (n + 1) s.L)
    let (s2, f) := s1.fact rb s.L ra 2 w ra n (seq.push 0)
    s := s2
    rab := 2 * f + 1
  let keep := min ra rb
  let kill := max ra rb
  let kref := if keep == ra then rab else rab ^^^ 1
  s := s.setPar kill keep
  s := s.setLref kill (kref ^^^ 1)
  s := { s with ncoinc := s.ncoinc + 1 }
  let L := s.L
  let mut row : Array (Option (Nat × Nat)) := #[]
  for c in [0:L] do
    row := row.push (s.entry kill c)
    s := s.setTab (kill * L + c) 0
  for c in [0:L] do
    match row[c]! with
    | none => pure ()
    | some (d, phi) =>
      let ci := s.inv[c]!
      if d == kill then
        let (s1, w) := s.wid [L, c, L, ci]
        let (s2, f) := s1.fact keep ci keep 2 w keep 3 #[kref, phi, kref ^^^ 1, 0]
        s := s2.put keep c keep (2 * f + 1)
      else
        match s.entry d ci with
        | some (e, _) => if e == kill then s := s.setTab (d * L + ci) 0
        | none => pure ()
        let (s1, w) := s.wid [L, c, ci]
        let (s2, f) := s1.fact d ci keep 2 w keep 2 #[kref, phi, 0]
        s := s2.put keep c d (2 * f + 1)
  return s

def process (s : St) (fuel : Nat := 100000000) : St := Id.run do
  let mut s := s
  for _ in [0:fuel] do
    if s.cq.size == 0 then break
    let (a, b, lam) := s.cq.back!
    let q := s.cq
    s := { s with cq := #[] }
    s := { s with cq := q.pop }
    s := s.mergeOne a b lam
  return s

def scan (s : St) (p : Nat) (w : Array Nat) (wi : Nat) (define : Bool) (kind : Nat)
    (fuel : Nat := 1000000) : St := Id.run do
  let k := w.size
  let mut s := s
  for _ in [0:fuel] do
    let mut cur := p
    let mut i := 0
    let mut frefs : Array Nat := #[]
    while i < k do
      match s.entry cur w[i]! with
      | none => break
      | some (q, r) =>
        cur := q
        frefs := frefs.push r
        i := i + 1
    let mut bcur := p
    let mut j := k
    let mut brefs : Array Nat := #[]
    while j > i do
      match s.entry bcur (s.inv[w[j - 1]!]!) with
      | none => break
      | some (x, r) =>
        brefs := brefs.push (r ^^^ 1)
        bcur := x
        j := j - 1
    if j == i then
      if cur != bcur then
        let w2 := (w.extract 0 i).toList ++ [s.L] ++ (w.extract i k).toList
        let rs := frefs.push 0 ++ brefs.reverse
        if kind == 2 then
          let (s1, wi2) := s.wid w2
          let (s2, f) := s1.fact cur s.L bcur 2 wi2 p i rs
          s := (s2.pushCq (cur, bcur, 2 * f)).process
        else
          let subs := s.subs
          let wi2 := subs.size
          s := { s with subs := subs.push w2 }
          let (s2, f) := s.fact cur s.L bcur 3 wi2 0 i rs
          s := (s2.pushCq (cur, bcur, 2 * f)).process
      return s
    if j == i + 1 then
      let c := w[i]!
      let rs := frefs.push 0 ++ brefs.reverse
      let (s1, f) := s.fact cur c bcur kind wi (if kind == 2 then p else 0) i rs
      s := (s1.put cur c bcur (2 * f)).process
      return s
    if !define then return s
    let (s1, _) := s.newPoint cur w[i]!
    s := s1
  return { s with fail := true }

def deduce (s : St) (fuel : Nat := 1000000000) : St := Id.run do
  let mut s := s
  for _ in [0:fuel] do
    if s.ds.size == 0 then break
    let (x, c) := s.ds.back!
    let d := s.ds
    s := { s with ds := #[] }
    s := { s with ds := d.pop }
    if s.alive x then
      match s.entry x c with
      | none => pure ()
      | some (y, _) =>
        for wi in s.rots[c]! do
          if s.alive x then
            s := s.scan x (s.rels[wi]!).toArray wi false 2
        if s.alive y then
          for wi in s.rots[s.inv[c]!]! do
            if s.alive y then
              s := s.scan y (s.rels[wi]!).toArray wi false 2
  return s

end St

def initState (L : Nat) (inv : Array Nat) (rels subs : List (List Nat)) : St := Id.run do
  let mut s : St := {
    L := L, inv := inv.push L, rels := #[], relIdx := {}, rots := Array.replicate L #[],
    subs := subs.toArray, pl := #[0], tab := Array.replicate L 0, par := #[0], lref := #[0],
    facts := #[], refs := #[], cq := #[], ds := #[], ncoinc := 0, fail := false }
  for r in rels do
    let (s1, _) := s.wid r
    s := s1
  let mut seen : Std.HashMap (List Nat) Unit := {}
  for r in rels do
    let rinv := r.reverse.map fun c => s.inv[c]!
    for rr in [r, rinv] do
      for i in [0:rr.length] do
        let t := rr.drop i ++ rr.take i
        if !seen.contains t then
          seen := seen.insert t ()
          let (s1, wi) := s.wid t
          s := s1
          match t with
          | [] => pure ()
          | c :: _ =>
            let ro := s.rots
            s := { s with rots := #[] }
            s := { s with rots := ro.modify c (·.push wi) }
  return s

def enumerate (L : Nat) (inv : Array Nat) (rels subs : List (List Nat)) (maxPts : Nat) : St :=
  Id.run do
  let mut s := initState L inv rels subs
  for wi in [0:subs.length] do
    s := (s.scan 0 (s.subs[wi]!).toArray wi true 3).deduce
  let mut p := 0
  for _ in [0:maxPts] do
    if p ≥ s.pl.size || s.fail then break
    if s.alive p then
      for c in [0:L] do
        if s.alive p && (s.entry p c).isNone then
          let (s1, _) := s.newPoint p c
          s := s1.deduce
    if s.pl.size > maxPts then
      s := { s with fail := true }
      break
    p := p + 1
  return s

def certOf (s : St) : Cert := Id.run do
  let N := s.pl.size
  let L := s.L
  let live := (Array.range N).map fun p => s.alive p
  let mut ffi : Array Nat := Array.replicate (N * L) 0
  let mut ok := !s.fail
  for i in [0:N] do
    if live[i]! then
      for c in [0:L] do
        match s.entry i c with
        | none => ok := false
        | some (j, r) =>
          if !live[j]! then ok := false
          ffi := ffi.set! (i * L + c) r
  return { N := N, L := L, pl := s.pl, facts := s.facts, refs := s.refs, rels := s.rels,
           subs := s.subs, live := live, ffi := ffi, ok := ok }

end CFSG.YGroups.Native
