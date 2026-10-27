module

public import Certificates.Data.D4HexOrb
public import Certificates.Data.D4HexGeoWords
public import Std.Data.HashMap

public section

namespace CFSG.D4Hex

open CFSG.Monster.B.Co2.Native

@[expose] def hexPtsOK (pts : Array Nat) : Bool :=
  pts.size == 3 * 2457 && allLt 2457 fun v =>
    decide (pts[3 * v]! < pts[3 * v + 1]!) && decide (pts[3 * v + 1]! < pts[3 * v + 2]!) &&
      decide (pts[3 * v + 2]! < 819)

@[expose] def hexOnLine (pts : Array Nat) (p v : Nat) : Bool :=
  pts[3 * v]! == p || pts[3 * v + 1]! == p || pts[3 * v + 2]! == p

@[expose] def hexPtL (pts : Array Nat) : Array Nat := Id.run do
  let mut bk : Array (Array Nat) := Array.replicate 819 #[]
  for v in [0:2457] do
    for k in [0:3] do
      bk := bk.modify pts[3 * v + k]! fun l => l.push v
  let mut out : Array Nat := #[]
  for p in [0:819] do
    for k in [0:9] do
      out := out.push (bk[p]!)[k]!
  return out

@[expose] def hexIncOK (pts ptL : Array Nat) : Bool :=
  (allLt 819 fun x => allLt 9 fun k =>
      decide (ptL[9 * x + k]! < 2457) && hexOnLine pts x ptL[9 * x + k]!) &&
    (allLt 2457 fun v => allLt 3 fun k =>
      (List.range 9).any fun j => ptL[9 * pts[3 * v + k]! + j]! == v)

@[expose] def hexMeetOK (pts ptL : Array Nat) : Bool :=
  allLt 819 fun x => allLt 9 fun i => allLt 9 fun j => i == j || allLt 3 fun a => allLt 3 fun b =>
    pts[3 * ptL[9 * x + i]! + a]! == x || pts[3 * ptL[9 * x + j]! + b]! == x ||
      pts[3 * ptL[9 * x + i]! + a]! != pts[3 * ptL[9 * x + j]! + b]!

@[expose] def hexNbr (pts ptL : Array Nat) (x : Nat) : List Nat :=
  if x < 819 then (List.range 9).map fun k => ptL[9 * x + k]! + 819
  else (List.range 3).map fun k => pts[3 * (x - 819) + k]!

@[expose] def hexLayBFS (pts ptL : Array Nat) (b : Nat) : Array Nat × Array Nat := Id.run do
  let mut lay : Array Nat := (Array.replicate 3276 255).set! b 0
  let mut par : Array Nat := Array.replicate 3276 0
  let mut q : Array Nat := #[b]
  for h in [0:3276] do
    if h < q.size then
      let x := q[h]!
      for y in hexNbr pts ptL x do
        if y < 3276 && lay[y]! == 255 then
          lay := lay.set! y (lay[x]! + 1)
          par := par.set! y x
          q := q.push y
  return (lay, par)

@[expose] def hexLayOK (pts ptL : Array Nat) (b : Nat) (lay par : Array Nat) : Bool :=
  decide (b < 3276) && lay[b]! == 0 && allLt 3276 fun x =>
    decide (lay[x]! ≤ 6) &&
    (x == b || (decide (par[x]! < 3276) && (hexNbr pts ptL x).contains par[x]! &&
      lay[par[x]!]! + 1 == lay[x]!)) &&
    (hexNbr pts ptL x).all (fun y => decide (lay[y]! ≤ lay[x]! + 1)) &&
    (lay[x]! == 0 || decide (5 < lay[x]!) ||
      (hexNbr pts ptL x).all fun y => lay[y]! + 1 != lay[x]! || y == par[x]!)

@[expose] def hexLineMaps (pts g : Array Nat) (v w : Nat) : Bool :=
  (List.range 3).all fun k => hexOnLine pts g[pts[3 * v + k]!]! w

@[expose] def hexActOK (pts g : Array Nat) (y x : Nat) : Bool :=
  if y < 819 then decide (x < 819) && g[y]! == x
  else decide (819 ≤ x) && decide (x < 3276) && hexLineMaps pts g (y - 819) (x - 819)

@[expose] def hexLineKeyMap (pts : Array Nat) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for v in [0:2457] do
    m := m.insert ((pts[3 * v]! * 819 + pts[3 * v + 1]!) * 819 + pts[3 * v + 2]!) v
  return m

@[expose] def hexActS (pts : Array Nat) (km : Std.HashMap Nat Nat) (A : Array (Array Nat))
    (j x : Nat) : Nat :=
  if x < 819 then (A[j]!)[x]!
  else
    let g := A[j]!
    let a := g[pts[3 * (x - 819)]!]!
    let b := g[pts[3 * (x - 819) + 1]!]!
    let c := g[pts[3 * (x - 819) + 2]!]!
    let p := if a ≤ b then (a, b) else (b, a)
    let q := if p.2 ≤ c then (p.2, c) else (c, p.2)
    let r := if p.1 ≤ q.1 then (p.1, q.1) else (q.1, p.1)
    819 + km.getD ((r.1 * 819 + r.2) * 819 + q.2) 3276

@[expose] def hexMkCycle (pts ptL : Array Nat) (b : Nat) : Array Nat :=
  let lp := hexLayBFS pts ptL b
  let lay := lp.1
  let par := lp.2
  let q := ((List.range 3276).find? fun x => lay[x]! == 6).getD 0
  let ps := (hexNbr pts ptL q).filter fun y => lay[y]! == 5
  let p1 := ps[0]!
  let p2 := ps[1]!
  let back (y : Nat) : List Nat :=
    (List.range 5).foldl (fun acc _ => par[acc.head!]! :: acc) [y]
  (back p1 ++ [q] ++ (back p2).tail!.reverse).toArray

@[expose] def hexCycleOK (pts ptL : Array Nat) (c : Array Nat) : Bool :=
  c.size == 12 && allLt 12 fun i =>
    decide (c[i]! < 3276) && (hexNbr pts ptL c[i]!).contains c[(i + 1) % 12]! &&
      c[i]! != c[(i + 2) % 12]!

@[expose] def orbOKR (N k : Nat) (act : Nat → Nat → Nat → Bool) (root cnt : Nat)
    (items : Nat → Bool) (r : OrbRec) : Bool :=
  r.ord.size == cnt && r.par.size == cnt && r.lab.size == cnt && r.ord[0]! == root &&
    (allLt cnt fun i => decide (r.ord[i]! < N)) &&
    (allLt cnt fun i => i == 0 || (decide (r.par[i]! < i) && decide (r.lab[i]! < k) &&
      act r.lab[i]! r.ord[r.par[i]!]! r.ord[i]!)) &&
    allLt N fun x => !items x || (decide (r.pos[x]! < cnt) && r.ord[r.pos[x]!]! == x)

@[expose] def hexDecode (s : String) : List Nat := s.toList.map fun c => c.toNat - 48

@[expose] def hexEvalArr (G : Array (Array Nat)) : List Nat → Array Nat
  | [] => idA 819
  | l :: w => compA 819 G[l]! (hexEvalArr G w)

@[expose] def hexWordArrs (G : Array (Array Nat)) (ws : List String) : Array (Array Nat) :=
  (ws.map fun s => hexEvalArr G (hexDecode s)).toArray

@[expose] def hexWordsOK (k : Nat) (ws : List String) : Bool :=
  ws.all fun s => (hexDecode s).all fun l => decide (l < k)

@[expose] def hexPtLocalOK (pts ptL : Array Nat) (G : Array (Array Nat)) (lay : Array Nat)
    (b0 : Nat) (hW pW : List String) : Bool :=
  let H := hexWordArrs G hW
  let P := hexWordArrs G pW
  let km := hexLineKeyMap pts
  hexWordsOK G.size hW && hexWordsOK G.size pW && decide (b0 < 819) && decide (lay[b0]! = 6) &&
    decide (((List.range 9).map fun k => ptL[k]!).Nodup) &&
    (allLt H.size fun i => H[i]![0]! == 0) &&
    orbOKR 3276 H.size (fun j y x => hexActOK pts H[j]! y x) b0 512 (fun x => lay[x]! == 6)
      (orbBFS 3276 H.size (hexActS pts km H) b0) &&
    (allLt P.size fun i => P[i]![0]! == 0 && P[i]![b0]! == b0) &&
    (List.range 9).all fun a => (List.range 9).all fun b => a == b ||
      (List.range P.size).any fun i =>
        hexActOK pts P[i]! (819 + ptL[0]!) (819 + ptL[a]!) &&
          hexActOK pts P[i]! (819 + ptL[1]!) (819 + ptL[b]!)

@[expose] def hexLnLocalOK (pts : Array Nat) (G : Array (Array Nat)) (lay : Array Nat)
    (y0 m0 : Nat) (nW tW : List String) : Bool :=
  let Nn := hexWordArrs G nW
  let T := hexWordArrs G tW
  let km := hexLineKeyMap pts
  let act := fun j y x => hexActOK pts Nn[j]! y x
  hexWordsOK G.size nW && hexWordsOK G.size tW && decide (y0 < 819) && decide (lay[y0]! = 5) &&
    decide (819 ≤ m0) && decide (m0 < 3276) && decide (lay[m0]! = 6) &&
    (allLt Nn.size fun i => hexActOK pts Nn[i]! 819 819) &&
    orbOKR 3276 Nn.size act y0 768 (fun x => lay[x]! == 5)
      (orbBFS 3276 Nn.size (hexActS pts km Nn) y0) &&
    orbOKR 3276 Nn.size act m0 2048 (fun x => lay[x]! == 6)
      (orbBFS 3276 Nn.size (hexActS pts km Nn) m0) &&
    (allLt T.size fun i => hexActOK pts T[i]! 819 819 && hexActOK pts T[i]! m0 m0) &&
    (List.range 3).all fun a => (List.range 3).all fun b => a == b ||
      (List.range T.size).any fun i => T[i]![pts[0]!]! == pts[a]! && T[i]![pts[1]!]! == pts[b]!

@[expose] def hexLinesOK (pts : Array Nat) (G : Array (Array Nat)) : Bool :=
  let km := hexLineKeyMap pts
  orbOKR 3276 G.size (fun j y x => hexActOK pts G[j]! y x) 819 2457
    (fun x => decide (819 ≤ x) && decide (x < 3276)) (orbBFS 3276 G.size (hexActS pts km G) 819)

@[expose] def d4GeoCheck (pts lay0 : Array Nat) (G : Array (Array Nat)) : Bool :=
  let ptL := hexPtL pts
  let lp0 := hexLayBFS pts ptL 0
  let lp1 := hexLayBFS pts ptL 819
  hexPtsOK pts && hexIncOK pts ptL && hexMeetOK pts ptL && decide (pts[0]! = 0) &&
    decide (G.size = 8) && decide (lay0.size = 819) && (allLt 819 fun x => lay0[x]! == lp0.1[x]!) &&
    hexLayOK pts ptL 0 lp0.1 lp0.2 && hexLayOK pts ptL 819 lp1.1 lp1.2 &&
    hexCycleOK pts ptL (hexMkCycle pts ptL 0) && hexLinesOK pts G &&
    hexPtLocalOK pts ptL G lp0.1 hexB0 hexHWords hexPWords &&
    hexLnLocalOK pts G lp1.1 hexY0 hexM0 hexNWords hexTWords

end CFSG.D4Hex
