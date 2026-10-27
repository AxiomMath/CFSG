module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

open Std

namespace Certificates.Census

set_option compiler.extract_closed false

def bitsOf (m : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut m := m
  while m != 0 do
    let low := m ^^^ (m &&& (m - 1))
    out := out.push (Nat.log2 low)
    m := m ^^^ low
  return out

def bit (i : Nat) : Nat := 1 <<< i
def hasBit (m i : Nat) : Bool := (m >>> i) % 2 == 1
def popc (m : Nat) : Nat := (bitsOf m).size
def imod3 (x : Int) : Nat := (x % 3).toNat

def dot3 (v w : Array Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:v.size] do
    s := s + v[i]! * w[i]!
  return s % 3

def dotI (v w : Array Int) : Int := Id.run do
  let mut s : Int := 0
  for i in [0:v.size] do
    s := s + v[i]! * w[i]!
  return s

def rowRed3 (rows : Array (Array Nat)) (nc : Nat) : Array (Array Nat) × Array Nat := Id.run do
  let mut R : Array (Array Nat) := rows.map (·.map (· % 3))
  let m := R.size
  let mut piv : Array Nat := #[]
  let mut k := 0
  for j in [0:nc] do
    if k < m then
      let mut q : Option Nat := none
      for i in [k:m] do
        if q.isNone && R[i]![j]! != 0 then q := some i
      match q with
      | none => pure ()
      | some qq =>
        let rk := R[k]!
        let rq := R[qq]!
        R := (R.set! k rq).set! qq rk
        let t := R[k]![j]!
        R := R.set! k (R[k]!.map fun x => (x * t) % 3)
        let rowk := R[k]!
        for i in [0:m] do
          if i != k && R[i]![j]! != 0 then
            let t := R[i]![j]!
            let rowi := R[i]!
            R := R.set! i (Array.ofFn (n := nc) fun c =>
              (rowi[c.val]! + 3 - (t * rowk[c.val]!) % 3) % 3)
        piv := piv.push j
        k := k + 1
  return (R.extract 0 k, piv)

def rank3 (rows : Array (Array Nat)) (nc : Nat) : Nat := (rowRed3 rows nc).2.size

def null3 (rows : Array (Array Nat)) (d : Nat) : Array (Array Nat) := Id.run do
  let (R, piv) := rowRed3 rows d
  let mut out : Array (Array Nat) := #[]
  for j in [0:d] do
    if !piv.contains j then
      let mut v : Array Nat := Array.ofFn (n := d) fun _ => 0
      v := v.set! j 1
      for i in [0:piv.size] do
        v := v.set! piv[i]! ((3 - R[i]![j]!) % 3)
      out := out.push v
  return out

def firstNZ (v : Array Nat) : Nat := Id.run do
  for x in v do
    if x % 3 != 0 then return x % 3
  return 0

def line3 (v : Array Nat) : Array Nat := let t := firstNZ v; v.map fun x => (x * t) % 3

def rankQ (rows : Array (Array Int)) : Nat := Id.run do
  let m := rows.size
  if m == 0 then return 0
  let n := rows[0]!.size
  let mut R := rows
  let mut r := 0
  for j in [0:n] do
    if r < m then
      let mut q : Option Nat := none
      for i in [r:m] do
        if q.isNone && R[i]![j]! != 0 then q := some i
      match q with
      | none => pure ()
      | some qq =>
        let rr := R[r]!
        let rq := R[qq]!
        R := (R.set! r rq).set! qq rr
        let rowr := R[r]!
        let p := rowr[j]!
        for i in [r+1:m] do
          let c := R[i]![j]!
          if c != 0 then
            let rowi := R[i]!
            let nr : Array Int := Array.ofFn (n := n) fun t => p * rowi[t.val]! - c * rowr[t.val]!
            let g := nr.foldl (fun g x => Nat.gcd g x.natAbs) 0
            R := R.set! i (if g > 1 then nr.map (· / (g : Int)) else nr)
        r := r + 1
  return r

def detInt (M : Array (Array Int)) : Int := Id.run do
  let n := M.size
  if n == 0 then return 1
  let mut A := M
  let mut sign : Int := 1
  let mut prev : Int := 1
  for k in [0:n-1] do
    if A[k]![k]! == 0 then
      let mut sw : Option Nat := none
      for i in [k+1:n] do
        if sw.isNone && A[i]![k]! != 0 then sw := some i
      match sw with
      | none => return 0
      | some i =>
        let t := A[k]!
        A := (A.set! k A[i]!).set! i t
        sign := -sign
    let rowk := A[k]!
    for i in [k+1:n] do
      let rowi := A[i]!
      let ni : Array Int := Array.ofFn (n := n) fun j =>
        if j.val > k then (rowi[j.val]! * rowk[k]! - rowi[k]! * rowk[j.val]!) / prev
        else rowi[j.val]!
      A := A.set! i ni
    prev := A[k]![k]!
  return sign * A[n-1]![n-1]!

abbrev IVec := Array Int

def vsub (r s : IVec) : IVec := Array.ofFn (n := r.size) fun i => r[i.val]! - s[i.val]!

def cartanMat (isF : Bool) (n : Nat) : Array (Array Int) := Id.run do
  let mut A : Array (Array Int) :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then 2 else 0
  let edges : List (Nat × Nat) :=
    if isF then [(0, 1), (1, 2), (2, 3)]
    else [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)] ++ (if n ≥ 7 then [(5, 6)] else []) ++
      (if n ≥ 8 then [(6, 7)] else [])
  for (i, j) in edges do
    A := A.set! i (A[i]!.set! j (-1))
    A := A.set! j (A[j]!.set! i (-1))
  if isF then A := A.set! 1 (A[1]!.set! 2 (-2))
  return A

def genRoots (A : Array (Array Int)) : Array IVec := Id.run do
  let n := A.size
  let simple : Array IVec :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then 1 else 0
  let mut seen : HashSet IVec := {}
  for s in simple do seen := seen.insert s
  let mut todo : Array IVec := simple
  let mut all : Array IVec := simple
  while todo.size > 0 do
    let r := todo.back!
    todo := todo.pop
    for i in [0:n] do
      let mut c : Int := 0
      for j in [0:n] do
        c := c + r[j]! * A[j]![i]!
      let s := r.set! i (r[i]! - c)
      if s.all (· ≥ 0) && !seen.contains s then
        seen := seen.insert s
        todo := todo.push s
        all := all.push s
  return all

def typeName (n k : Nat) : Nat × Nat :=
  if k == n * (n + 1) / 2 then (0, n)
  else if k == n * (n - 1) && n ≥ 4 then (1, n)
  else if (n == 6 && k == 36) || (n == 7 && k == 63) || (n == 8 && k == 120) then (2, n)
  else if n == 4 && k == 24 then (3, 4)
  else if k == n * n then (4, n)
  else (9, n)

def gramB (B : Array (Array Int)) (r s : IVec) : Int := Id.run do
  let mut t : Int := 0
  for i in [0:r.size] do
    for j in [0:r.size] do
      t := t + r[i]! * B[i]![j]! * s[j]!
  return t

def permVec (rho : Array Nat) (r : IVec) : IVec :=
  Array.ofFn (n := r.size) fun j => r[rho[j.val]!]!

def coordsIn (emb : Array (Array Nat)) (hv : Array Nat) (n : Nat) : Option (Array Nat) :=
  let m := emb.size
  let aug : Array (Array Nat) :=
    Array.ofFn (n := n) fun i => (emb.map (·[i.val]!)).push hv[i.val]!
  let (red, piv) := rowRed3 aug (m + 1)
  if piv == Array.ofFn (n := m) (·.val) then some (red.map (·.back!)) else none

structure Data where
  mode : Nat
  n : Nat
  d : Nat
  N : Nat
  AR : Array IVec
  rho : Array Nat
  R : Array IVec
  absidx : Array (Array Nat)
  F : Array (Array Nat)
  H : Array (Array Nat)
  ix : HashMap IVec Nat
  aix : HashMap IVec Nat
  G : Array (Array Int)
  adj : Array Nat
  aadj : Array Nat
  refl : Array (Array Nat)
  lines : Array (Array Nat)
  full : Nat

def mkData (mode : Nat) : Option Data := Id.run do
  let isF := mode == 0
  let n : Nat := if isF then 4 else if mode == 4 then 7 else if mode == 5 then 8 else 6
  let A := cartanMat isF n
  let AR := genRoots A
  let rho : Array Nat := if mode == 1 then #[5, 1, 4, 3, 2, 0] else Array.ofFn (n := n) (·.val)
  let sc : Array Int := if isF then #[2, 2, 1, 1] else Array.ofFn (n := n) fun _ => 1
  let B : Array (Array Int) :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => A[i.val]![j.val]! * sc[j.val]!
  let mut ok := true
  let mut R : Array IVec := #[]
  let mut absidx : Array (Array Nat) := #[]
  let mut F : Array (Array Nat) := #[]
  let mut H : Array (Array Nat) := #[]
  let mut d := 0
  if mode == 1 then
    let emb : Array (Array Nat) :=
      #[#[1, 0, 0, 0, 0, 1], #[0, 0, 1, 0, 1, 0], #[0, 1, 0, 0, 0, 0], #[0, 0, 0, 1, 0, 0]]
    let mut groups : HashMap IVec (Array Nat) := {}
    let mut keys : Array IVec := #[]
    for i in [0:AR.size] do
      let r := AR[i]!
      let rr : IVec := Array.ofFn (n := n) fun j => r[j.val]! + r[rho[j.val]!]!
      if !groups.contains rr then keys := keys.push rr
      groups := groups.insert rr ((groups.getD rr #[]).push i)
    R := keys
    for rr in R do
      let grp := groups.getD rr #[]
      absidx := absidx.push grp
      let r := AR[grp[0]!]!
      F := F.push (emb.map fun v => Id.run do
        let mut t : Int := 0
        for i in [0:n] do
          for j in [0:n] do
            t := t + r[i]! * A[i]![j]! * ((v[j]! : Nat) : Int)
        return imod3 t)
      let hv := if grp.size == 2 then rr else r
      H := H.push #[imod3 hv[0]!, imod3 hv[2]!, imod3 hv[1]!, imod3 hv[3]!]
    d := 4
  else
    R := AR
    absidx := AR.mapIdx fun i _ => #[i]
    let emb : Array (Array Nat) :=
      if mode == 3 then Id.run do
        let mut e : Array (Array Nat) := #[]
        for i in [0:n] do
          let c : Array Nat := Array.ofFn (n := n) fun j => imod3 A[j.val]![i]!
          if rank3 (e.push c) n > e.size then e := e.push c
        return e
      else Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j => if i.val == j.val then 1 else 0
    d := emb.size
    for r in AR do
      let norm := gramB B r r
      let h : IVec := Array.ofFn (n := n) fun i => 2 * r[i.val]! * sc[i.val]! / norm
      let f : IVec :=
        if mode == 2 || mode == 3 then r
        else Array.ofFn (n := n) fun j => Id.run do
          let mut t : Int := 0
          for i in [0:n] do
            t := t + r[i]! * A[i]![j.val]!
          return t
      let hv : Array Nat :=
        if mode == 2 || mode == 3 then
          Array.ofFn (n := n) fun i => Id.run do
            let mut t : Int := 0
            for j in [0:n] do
              t := t + A[i.val]![j]! * h[j]!
            return imod3 t
        else h.map imod3
      F := F.push (emb.map fun v => imod3 (dotI f (v.map (fun (x : Nat) => (x : Int)))))
      match coordsIn emb hv n with
      | some c => H := H.push c
      | none => ok := false
  let N := R.size
  let mut ix : HashMap IVec Nat := {}
  for i in [0:N] do ix := ix.insert R[i]! i
  let mut aix : HashMap IVec Nat := {}
  for i in [0:AR.size] do aix := aix.insert AR[i]! i
  if !(F.all fun f => f.any (· != 0)) then ok := false
  let mut hs : HashSet (Array Nat) := {}
  for h in H do
    for s in [1, 2] do
      hs := hs.insert (h.map fun x => x * s % 3)
  if hs.size != 2 * N then ok := false
  let G : Array (Array Int) := R.map fun r => R.map fun s => gramB B r s
  for i in [0:N] do
    for j in [0:N] do
      if (dot3 F[i]! H[j]! : Int) != (2 * G[i]![j]! / G[j]![j]!) % 3 then ok := false
  let adj : Array Nat := Array.ofFn (n := N) fun i =>
    (List.range N).foldl (fun m j => if G[i.val]![j]! != 0 then m ||| bit j else m) 0
  let aadj : Array Nat := Array.ofFn (n := AR.size) fun i =>
    (List.range AR.size).foldl
      (fun m j => if gramB B AR[i.val]! AR[j]! != 0 then m ||| bit j else m) 0
  let mut refl : Array (Array Nat) := #[]
  for i in [0:N] do
    let r := R[i]!
    let mut row : Array Nat := #[]
    for j in [0:N] do
      let s := R[j]!
      let a := 2 * G[j]![i]!
      let b := G[i]![i]!
      if a % b != 0 then ok := false
      let q := a / b
      let z : IVec := Array.ofFn (n := n) fun t => s[t.val]! - q * r[t.val]!
      let neg := (z.find? (· != 0)).getD 0 < 0
      let z := if neg then z.map (- ·) else z
      match ix[z]? with
      | some k => row := row.push k
      | none => ok := false; row := row.push 0
    refl := refl.push row
  let all : Array (Array Nat) :=
    Array.ofFn (n := 3 ^ d) fun k => Array.ofFn (n := d) fun i => (k.val / 3 ^ (d - 1 - i.val)) % 3
  let lines := all.filter fun v => firstNZ v == 1
  let full := (1 <<< N) - 1
  if !ok then return none
  return some { mode, n, d, N, AR, rho, R, absidx, F, H, ix, aix, G, adj, aadj, refl, lines, full }

def zerosOf (dt : Data) (v : Array Nat) : Nat := Id.run do
  let mut m := 0
  for i in [0:dt.N] do
    if dot3 v dt.F[i]! == 0 then m := m ||| bit i
  return m

def comps (adj : Array Nat) (mask : Nat) : Array Nat := Id.run do
  let mut left := mask
  let mut out : Array Nat := #[]
  while left != 0 do
    let c0 := left ^^^ (left &&& (left - 1))
    left := left ^^^ c0
    let mut c := c0
    let mut front := c0
    while front != 0 do
      let mut nb := 0
      for i in bitsOf front do
        nb := nb ||| adj[i]!
      nb := nb &&& left
      left := left ^^^ nb
      c := c ||| nb
      front := nb
    out := out.push c
  return out

def rootsOfMask (R : Array IVec) (m : Nat) : Array IVec := (bitsOf m).map (R[·]!)

def simpOf (dt : Data) (mask : Nat) : Array Nat :=
  let ids := bitsOf mask
  ids.filter fun i =>
    !(ids.any fun j => j != i && match dt.ix[vsub dt.R[i]! dt.R[j]!]? with
        | some k => hasBit mask k
        | none => false)

def kindOf (dt : Data) (mask : Nat) : Nat × Nat :=
  typeName (rankQ (rootsOfMask dt.R mask)) (popc mask)

abbrev Label := Nat × Bool × Nat × Nat

def labelPure (dt : Data) (mask : Nat) : Label := Id.run do
  let ai : Nat := (bitsOf mask).foldl
    (fun acc i => (dt.absidx[i]!).foldl (fun a j => a ||| bit j) acc) 0
  let cs := comps dt.aadj ai
  if cs.size > 1 then
    if dt.mode == 1 && cs.size == 2 then
      let c0 := cs[0]!
      let (t, n) := typeName (rankQ (rootsOfMask dt.AR c0)) (popc c0)
      return (t, false, n, 2)
    else return (99, false, 0, 0)
  let c := cs[0]!
  let rts := rootsOfMask dt.AR c
  let (t, n) := typeName (rankQ rts) (popc c)
  let moved : Bool :=
    if dt.mode == 1 then
      rts.any fun r =>
        (!(rts.any fun s => s != r && match dt.aix[vsub r s]? with
            | some k => hasBit c k
            | none => false)) && permVec dt.rho r != r
    else false
  let opp := (t == 0 && n ≥ 2) || (t == 1 && n % 2 == 1) || (t == 2 && n == 6)
  return (t, opp != moved, n, 1)

structure Cache where
  lab : HashMap Nat Label
  ker : HashMap Nat (Array (Array Nat))
  bad : Bool

abbrev CM := StateM Cache

def kernelM (dt : Data) (m : Nat) : CM (Array (Array Nat)) := do
  match (← get).ker[m]? with
  | some k => return k
  | none =>
    let k := null3 ((bitsOf m).map (dt.F[·]!)) dt.d
    modify fun c => { c with ker := c.ker.insert m k }
    return k

def markBad : CM Unit := modify fun c => { c with bad := true }

def closureOf (dt : Data) (ids : Array Nat) : Nat := Id.run do
  let mut seen : Nat := ids.foldl (fun m i => m ||| bit i) 0
  let mut todo : Array Nat := ids
  while todo.size > 0 do
    let j := todo.back!
    todo := todo.pop
    for i in ids do
      let k := dt.refl[i]![j]!
      if !hasBit seen k then
        seen := seen ||| bit k
        todo := todo.push k
  return seen

def extensions (dt : Data) (common X : Nat) : Array (Nat × Int) := Id.run do
  let ss := simpOf dt common
  if ss.size + 1 != (kindOf dt X).2 then return #[]
  let mut out : Array (Nat × Int) := #[]
  for i in bitsOf (X ^^^ (X &&& common)) do
    for sg in [(1 : Int), -1] do
      if ss.all (fun j => sg * dt.G[i]![j]! ≤ 0) && closureOf dt (ss.push i) == X then
        out := out.push (i, sg)
  return out

def diagram (dt : Data) (V : Array (Nat × Int)) : Option (Array (Array Int) × Int) := Id.run do
  let m := V.size
  let C : Array (Array Int) := Array.ofFn (n := m) fun a => Array.ofFn (n := m) fun b =>
    2 * V[a.val]!.2 * V[b.val]!.2 * dt.G[V[a.val]!.1]![V[b.val]!.1]! /
      dt.G[V[b.val]!.1]![V[b.val]!.1]!
  for i in [0:m] do
    for j in [0:m] do
      if i != j && C[i]![j]! > 0 then return none
  let dd := detInt C
  if dd ≤ 0 then return none
  let mut seen : Nat := 1
  let mut todo : Array Nat := #[0]
  while todo.size > 0 do
    let i := todo.back!
    todo := todo.pop
    for j in [0:m] do
      if !hasBit seen j && i != j && C[i]![j]! != 0 then
        seen := seen ||| bit j
        todo := todo.push j
  if popc seen != m then return none
  let mut att := 0
  for j in [0:m-1] do
    if C[m-1]![j]! != 0 then att := att + 1
  if att != 1 then return none
  return some (C, dd)

def modelM (dt : Data) (L K : Nat) : CM Bool := do
  let common := L &&& K
  let ss : Array (Nat × Int) := (simpOf dt common).map fun i => (i, 1)
  let eL := extensions dt common L
  let eK := extensions dt common K
  for b in eL do
    for a in eK do
      let V := (ss.push b).push a
      match diagram dt V with
      | none => pure ()
      | some _ =>
        let kL ← kernelM dt L
        let kK ← kernelM dt K
        if !(kL.size == 1 && kK.size == 1) then markBad
        let idsL := (V.extract 0 (V.size - 1)).map (·.1)
        let idsK := ((V.extract 0 (V.size - 2)).push V[V.size - 1]!).map (·.1)
        if closureOf dt idsL != L || closureOf dt idsK != K then markBad
        return true
  return false

def ambientM (dt : Data) (J L K : Nat) : CM (Option ((Nat × Nat) × Int × Int)) := do
  let psi := closureOf dt (bitsOf (L ||| K))
  for b in extensions dt J L do
    let ss : Array (Nat × Int) := ((simpOf dt J).map fun i => (i, (1 : Int))).push b
    for i in bitsOf (psi ^^^ (psi &&& L)) do
      for sg in [(1 : Int), -1] do
        let V := ss.push (i, sg)
        match diagram dt V with
        | none => pure ()
        | some (C, dd) =>
          if dd % 3 == 0 || V.size != dt.d then continue
          let Cl : Array (Array Int) :=
            (C.extract 0 (C.size - 1)).map fun r => r.extract 0 (r.size - 1)
          let dl := detInt Cl
          if dl % 3 == 0 then continue
          if closureOf dt (V.map (·.1)) != psi then continue
          if rank3 (V.map fun v => dt.H[v.1]!) dt.d != dt.d then markBad
          if closureOf dt ((V.extract 0 (V.size - 1)).map (·.1)) != L then markBad
          return some (kindOf dt psi, dd, dl)
  return none

end Certificates.Census
