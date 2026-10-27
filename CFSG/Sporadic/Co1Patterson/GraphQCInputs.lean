module

public import CFSG.Sporadic.Co1Patterson.GraphInputs

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1Block

@[expose] def xeK (o : Orb) (k : Nat) : Rows := mul o.hs[k]! (repX 1)

@[expose] def xeiK (o : Orb) (k : Nat) : Rows := mul (repXi 1) o.his[k]!

@[expose] def adjC (S : Std.HashSet (Array Nat)) (X Xi V : Rows) : Bool :=
  S.contains (mul (mul Xi V) X)

@[expose] def vtxR (X Xi : Rows) : Rows := conjA X Xi

@[expose] def nbrX (o : Orb) (p : Rows × Rows) (k : Nat) : Rows × Rows :=
  (mul p.1 (xeK o k), mul (xeiK o k) p.2)

@[expose] def ord6 (M : Rows) : Nat :=
  let p2 := mul M M
  let p3 := mul p2 M
  let p4 := mul p3 M
  let p5 := mul p4 M
  let p6 := mul p5 M
  if M == one then 1 else if p2 == one then 2 else if p3 == one then 3 else
    if p4 == one then 4 else if p5 == one then 5 else if p6 == one then 6 else 0

@[expose] def dcls (S : Std.HashSet (Array Nat)) (V : Rows) : Nat :=
  if V == iotaARows then 0 else if S.contains V then 1 else
    let M := mul iotaARows V
    let o := ord6 M
    if o == 2 || o == 4 || o == 6 then 2 else if o == 5 then 3 else
      if o == 3 then (if fixDimIs M 12 then 2 else if fixDimIs M 8 then 3 else 9) else 9

inductive PC where
  | chord (r : Nat)
  | centre (r k : Nat)
  | split (r k : Nat) (P : PC)
deriving Inhabited

inductive QC where
  | pent (c c' : Nat) (P : PC)
  | prop (k : Nat) (C₁ C₂ : QC)
deriving Inhabited

@[expose] def pv (vs : Array (Rows × Rows)) (i : Nat) : Rows × Rows := vs[i % 5]!

@[expose] def pcOK (o : Orb) (S : Std.HashSet (Array Nat)) :
    Array (Rows × Rows) → PC → Bool
  | vs, .chord r =>
    let u := pv vs r
    let w := pv vs (r + 2)
    vtxR u.1 u.2 == vtxR w.1 w.2 || adjC S u.1 u.2 (vtxR w.1 w.2)
  | vs, .centre r k =>
    let z := nbrX o (pv vs r) k
    decide (k < o.c.pts.size) && adjC S z.1 z.2 (vtxR (pv vs (r + 2)).1 (pv vs (r + 2)).2) &&
      adjC S z.1 z.2 (vtxR (pv vs (r + 3)).1 (pv vs (r + 3)).2)
  | vs, .split r k P =>
    let z := nbrX o (pv vs r) k
    decide (k < o.c.pts.size) && adjC S z.1 z.2 (vtxR (pv vs (r + 2)).1 (pv vs (r + 2)).2) &&
      pcOK o S #[pv vs r, z, pv vs (r + 2), pv vs (r + 3), pv vs (r + 4)] P

@[expose] def qcOK (o : Orb) (S : Std.HashSet (Array Nat)) :
    (Rows × Rows) → (Rows × Rows) → QC → Bool
  | b, g, .pent c c' P =>
    let pc := (xeK o c, xeiK o c)
    let pc' := (xeK o c', xeiK o c')
    decide (c < o.c.pts.size) && decide (c' < o.c.pts.size) &&
      adjC S pc.1 pc.2 (vtxR b.1 b.2) && adjC S g.1 g.2 (vtxR pc'.1 pc'.2) &&
      pcOK o S #[(one, one), pc, b, g, pc'] P
  | b, g, .prop k C₁ C₂ =>
    let x := nbrX o b k
    decide (k < o.c.pts.size) && adjC S x.1 x.2 (vtxR g.1 g.2) && qcOK o S b x C₁ &&
      qcOK o S x g C₂

@[expose] def treeIn (o : Orb) (S : Std.HashSet (Array Nat)) (ns ps : List Nat)
    (P Q : Nat → Bool) : Bool :=
  let nsA := ns.toArray
  let psA := ps.toArray
  let nset : Std.HashSet Nat := Std.HashSet.ofList ns
  decide (0 < nsA.size) && psA.size == nsA.size &&
    (List.range nsA.size).all (fun t =>
      decide (nsA[t]! < o.c.pts.size) && P nsA[t]! &&
        (t == 0 || (decide (psA[t]! < t) &&
          adjC S (xeK o nsA[t]!) (xeiK o nsA[t]!) o.c.pts[nsA[psA[t]!]!]!))) &&
    (List.range o.c.pts.size).all (fun k => !(Q k) || nset.contains k)

@[expose] def atK (o : Orb) (k : Nat) (B : Rows) : Rows := mul (mul (xeiK o k) B) (xeK o k)

end CFSG.Sporadic.Co1Patterson.Native
