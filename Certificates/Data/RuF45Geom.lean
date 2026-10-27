module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap

public section

namespace CFSG.RuF45

open CFSG.Monster.B.Co2.Native

abbrev Word := List (Nat × Bool)

@[expose] def lettArr (G Gi : Array (Array Nat)) (l : Nat × Bool) : Array Nat :=
  if l.2 then G[l.1]! else Gi[l.1]!

@[expose] def evalArr (n : Nat) (G Gi : Array (Array Nat)) : Word → Array Nat
  | [] => idA n
  | l :: w => compA n (lettArr G Gi l) (evalArr n G Gi w)

@[expose] def decodeWord (s : String) : Word :=
  s.toList.map fun c => ((c.toNat - 48) / 2, (c.toNat - 48) % 2 == 0)

@[expose] def invArrs (n : Nat) (G : Array (Array Nat)) : Array (Array Nat) :=
  G.map (invCand n)

@[expose] def invsOK (n : Nat) (G Gi : Array (Array Nat)) : Bool :=
  G.size == Gi.size && allLt G.size fun i => isInvA n G[i]! Gi[i]!

@[expose] def ptsOK (pts : Array Nat) : Bool :=
  pts.size == 3 * 2925 && allLt 2925 fun v =>
    decide (pts[3 * v]! < pts[3 * v + 1]!) && decide (pts[3 * v + 1]! < pts[3 * v + 2]!) &&
      decide (pts[3 * v + 2]! < 1755)

@[expose] def onLineP (pts : Array Nat) (p v : Nat) : Bool :=
  pts[3 * v]! == p || pts[3 * v + 1]! == p || pts[3 * v + 2]! == p

@[expose] def mkPtL (pts : Array Nat) : Array Nat := Id.run do
  let mut bk : Array (Array Nat) := Array.replicate 1755 #[]
  for v in [0:2925] do
    for k in [0:3] do
      bk := bk.modify pts[3 * v + k]! fun l => l.push v
  let mut out : Array Nat := #[]
  for p in [0:1755] do
    for k in [0:5] do
      out := out.push (bk[p]!)[k]!
  return out

@[expose] def incOK (pts ptL : Array Nat) : Bool :=
  (allLt 1755 fun x => allLt 5 fun k =>
      decide (ptL[5 * x + k]! < 2925) && onLineP pts x ptL[5 * x + k]!) &&
    (allLt 2925 fun v => allLt 3 fun k =>
      (List.range 5).any fun j => ptL[5 * pts[3 * v + k]! + j]! == v)

@[expose] def nbrL (pts ptL : Array Nat) (x : Nat) : List Nat :=
  if x < 1755 then (List.range 5).map fun k => ptL[5 * x + k]! + 1755
  else (List.range 3).map fun k => pts[3 * (x - 1755) + k]!

@[expose] def layBFS (pts ptL : Array Nat) (b : Nat) : Array Nat × Array Nat := Id.run do
  let mut lay : Array Nat := (Array.replicate 4680 255).set! b 0
  let mut par : Array Nat := Array.replicate 4680 0
  let mut q : Array Nat := #[b]
  for h in [0:4680] do
    if h < q.size then
      let x := q[h]!
      for y in nbrL pts ptL x do
        if y < 4680 && lay[y]! == 255 then
          lay := lay.set! y (lay[x]! + 1)
          par := par.set! y x
          q := q.push y
  return (lay, par)

@[expose] def layOK (pts ptL : Array Nat) (b : Nat) (lay par : Array Nat) : Bool :=
  decide (b < 4680) && lay[b]! == 0 && allLt 4680 fun x =>
    decide (lay[x]! ≤ 8) &&
    (x == b || (decide (par[x]! < 4680) && (nbrL pts ptL x).contains par[x]! &&
      lay[par[x]!]! + 1 == lay[x]!)) &&
    (nbrL pts ptL x).all (fun y => decide (lay[y]! ≤ lay[x]! + 1)) &&
    (lay[x]! == 0 || decide (7 < lay[x]!) ||
      (nbrL pts ptL x).all fun y => lay[y]! + 1 != lay[x]! || y == par[x]!)

@[expose] def cnt8 (lay : Array Nat) : Nat := (List.range 4680).countP fun x => lay[x]! == 8

@[expose] def lineMapsP (pts g : Array Nat) (v w : Nat) : Bool :=
  (List.range 3).all fun k => onLineP pts g[pts[3 * v + k]!]! w

@[expose] def actOK (pts g : Array Nat) (y x : Nat) : Bool :=
  if y < 1755 then decide (x < 1755) && g[y]! == x
  else decide (1755 ≤ x) && decide (x < 4680) && lineMapsP pts g (y - 1755) (x - 1755)

@[expose] def lineKeyMap (pts : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for v in [0:2925] do
    m := m.insert ((pts[3 * v]! * 1755 + pts[3 * v + 1]!) * 1755 + pts[3 * v + 2]!) v
  return m

@[expose] def actS (pts : Array Nat) (km : Std.HashMap Nat Nat) (A : Array (Array Nat))
    (j x : Nat) : Nat :=
  if x < 1755 then (A[j]!)[x]!
  else
    let g := A[j]!
    let a := g[pts[3 * (x - 1755)]!]!
    let b := g[pts[3 * (x - 1755) + 1]!]!
    let c := g[pts[3 * (x - 1755) + 2]!]!
    let p := if a ≤ b then (a, b) else (b, a)
    let q := if p.2 ≤ c then (p.2, c) else (c, p.2)
    let r := if p.1 ≤ q.1 then (p.1, q.1) else (q.1, p.1)
    1755 + km.getD ((r.1 * 1755 + r.2) * 1755 + q.2) 4680

@[expose] def mkCycle (pts ptL : Array Nat) (b : Nat) : Array Nat :=
  let lp := layBFS pts ptL b
  let lay := lp.1
  let par := lp.2
  let q := ((List.range 4680).find? fun x => lay[x]! == 8).getD 0
  let ps := (nbrL pts ptL q).filter fun y => lay[y]! == 7
  let p1 := ps[0]!
  let p2 := ps[1]!
  let back (y : Nat) : List Nat :=
    (List.range 7).foldl (fun acc _ => par[acc.head!]! :: acc) [y]
  (back p1 ++ [q] ++ (back p2).tail!.reverse).toArray

@[expose] def cycleOK (pts ptL : Array Nat) (c : Array Nat) : Bool :=
  c.size == 16 && allLt 16 fun i =>
    decide (c[i]! < 4680) && (nbrL pts ptL c[i]!).contains c[(i + 1) % 16]! &&
      c[i]! != c[(i + 2) % 16]!

end CFSG.RuF45
