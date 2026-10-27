module

public import Certificates.Data.CFSGNative.Perm.Chain
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.J1.Native

open CFSG.Sporadic.Th.Native

@[expose] def dotL : List Nat → List Nat → Nat
  | a :: r, b :: c => a * b + dotL r c
  | _, _ => 0

@[expose] def mvL (p : Nat) (X : List (List Nat)) (v : List Nat) : List Nat :=
  X.map fun r => dotL r v % p

@[expose] def colsL (d : Nat) (Y : List (List Nat)) : List (List Nat) :=
  (List.range d).map fun j => Y.map fun r => r.getD j 0

@[expose] def mulL (p d : Nat) (X Y : List (List Nat)) : List (List Nat) :=
  X.map fun r => (colsL d Y).map fun c => dotL r c % p

@[expose] def idL (d : Nat) : List (List Nat) :=
  (List.range d).map fun i => (List.range d).map fun j => if i = j then 1 else 0

@[expose] def powL (p d : Nat) (X : List (List Nat)) : Nat → List (List Nat)
  | 0 => idL d
  | e + 1 => mulL p d X (powL p d X e)

@[expose] def wfM (d : Nat) (X : List (List Nat)) : Bool :=
  X.length == d && X.all fun r => r.length == d

@[expose] def wfV (p d : Nat) (v : List Nat) : Bool :=
  v.length == d && v.all fun x => x < p

@[expose] def negL (p : Nat) (v : List Nat) : List Nat := v.map fun x => (p - x) % p

@[expose] def firstNZ : List Nat → Nat
  | [] => 0
  | a :: r => if a == 0 then firstNZ r else a

@[expose] def sgnKey (p : Nat) (v : List Nat) : List Nat :=
  if firstNZ v ≤ (p - 1) / 2 then v else negL p v

@[expose] def colMat (d : Nat) (vs : List (List Nat)) : List (List Nat) :=
  (List.range d).map fun i => vs.map fun v => v.getD i 0

@[expose] def invMod (p x : Nat) : Nat := x ^ (p - 2) % p

@[expose] def gaussInv (p d : Nat) (X : List (List Nat)) : List (List Nat) := Id.run do
  let mut m : Array (Array Nat) := (X.map fun r => r.toArray).toArray
  let mut r : Array (Array Nat) := ((idL d).map fun r => r.toArray).toArray
  for c in [0:d] do
    let mut piv := d
    for i in [c:d] do
      if piv == d && (m[i]!)[c]! % p != 0 then piv := i
    if piv < d then
      let mp := m[piv]!
      let rp := r[piv]!
      m := (m.set! piv m[c]!).set! c mp
      r := (r.set! piv r[c]!).set! c rp
      let iv := invMod p (mp[c]! % p)
      let mc := mp.map fun x => x * iv % p
      let rc := rp.map fun x => x * iv % p
      m := m.set! c mc
      r := r.set! c rc
      for i in [0:d] do
        let f := (m[i]!)[c]! % p
        if i != c && f != 0 then
          m := m.set! i ((m[i]!).zipWith (fun x y => (x + (p - f) * y) % p) mc)
          r := r.set! i ((r[i]!).zipWith (fun x y => (x + (p - f) * y) % p) rc)
  return (r.map fun row => row.toList).toList

structure Orb where
  pts : Array (List Nat)
  alpha : Table
  beta : Table
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def orbBFS (p : Nat) (key : List Nat → List Nat) (A B : List (List Nat))
    (root : List Nat) (cap : Nat) : Orb := Id.run do
  let mut idx : Std.HashMap (List Nat) Nat := {}
  idx := idx.insert root 0
  let mut pts : Array (List Nat) := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut al : Table := #[]
  let mut be : Table := #[]
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      let wa := key (mvL p A v)
      match idx.get? wa with
      | some j => al := al.push (UInt32.ofNat j)
      | none =>
        idx := idx.insert wa pts.size
        al := al.push (UInt32.ofNat pts.size)
        pts := pts.push wa
        par := par.push h
        lab := lab.push 1
      let wb := key (mvL p B v)
      match idx.get? wb with
      | some j => be := be.push (UInt32.ofNat j)
      | none =>
        idx := idx.insert wb pts.size
        be := be.push (UInt32.ofNat pts.size)
        pts := pts.push wb
        par := par.push h
        lab := lab.push 2
    else break
  return ⟨pts, al, be, par, lab⟩

@[inline, expose] def orbCheckAt (p d : Nat) (rel : List Nat → List Nat → Bool)
    (A B : List (List Nat)) (O : Orb) (i : Nat) : Bool :=
  let n := O.pts.size
  let v := O.pts[i]!
  let a := ap O.alpha i
  let b := ap O.beta i
  wfV p d v && a < n && b < n && rel (mvL p A v) O.pts[a]! && rel (mvL p B v) O.pts[b]! &&
    (i == 0 || (O.par[i]! < i &&
      ((O.lab[i]! == 1 && ap O.alpha O.par[i]! == i) ||
        (O.lab[i]! == 2 && ap O.beta O.par[i]! == i))))

@[expose] def orbOK (p d : Nat) (rel : List Nat → List Nat → Bool) (A B : List (List Nat))
    (root : List Nat) (O : Orb) : Bool :=
  0 < O.pts.size && O.pts.size < 2 ^ 32 && O.pts[0]! == root && O.alpha.size == O.pts.size &&
    O.beta.size == O.pts.size && allIn 0 O.pts.size (orbCheckAt p d rel A B O)

@[expose] def eqRel (w v : List Nat) : Bool := w == v

@[expose] def pmRel (p : Nat) (w v : List Nat) : Bool := w == v || w == negL p v

@[expose] def vecSep (pts : Array (List Nat)) : Bool :=
  allIn 0 pts.size fun i => allIn (i + 1) pts.size fun j => pts[i]! != pts[j]!

@[expose] def minorNZ (p d : Nat) (u w : List Nat) : Bool :=
  (List.range d).any fun a => (List.range d).any fun b =>
    u.getD a 0 * w.getD b 0 % p != u.getD b 0 * w.getD a 0 % p

@[expose] def pmSep (p d : Nat) (pts : Array (List Nat)) (chunks : Nat) : Bool :=
  parAll pts.size chunks fun i => allIn (i + 1) pts.size fun j => minorNZ p d pts[i]! pts[j]!

@[expose] def genTables (O : Orb) (z : Int) : Table :=
  if z = 1 then O.alpha else if z = -1 then invT O.pts.size O.alpha
  else if z = 2 then O.beta else invT O.pts.size O.beta

end CFSG.Sporadic.J1.Native
