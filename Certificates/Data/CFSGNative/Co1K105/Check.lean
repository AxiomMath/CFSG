module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.KD.Co1K105

open CFSG.Sporadic.SmallF2.Native

@[expose] def t24Codes : List (Nat × Nat) :=
  [(145, 19049461067090809466252873200666015961935189),
   (125, 30186669490188212324833515829496339306),
   (123, 4541745440266336267019832564003460459),
   (113, 8877899011685098669842919838112437)]

@[expose] def wordOf (len code : Nat) : List Bool := (List.range len).map fun k => code.testBit k

@[expose] def mulM (M N : Array Nat) : Array Nat := mulRows 11 N M

@[expose] def wordM (cA cB : Array Nat) (w : List Bool) : Array Nat :=
  w.foldl (fun acc c => mulM acc (if c then cB else cA)) (idRows 11)

@[expose] def gensOf (Aa Ba : Array Nat) (codes : List (Nat × Nat)) : Array (Array Nat) :=
  let cA := transposeRows 11 Aa
  let cB := transposeRows 11 Ba
  (codes.map fun c => wordM cA cB (wordOf c.1 c.2)).toArray

@[expose] def keyM (M : Array Nat) : Nat := M.foldl (fun acc c => acc * 2048 + c) 0

@[expose] def enumT (gens : Array (Array Nat)) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let one := idRows 11
  let mut els : Array (Array Nat) := #[one]
  let mut par : Array Nat := #[0]
  let mut pg : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (keyM one)
  for h in [0:cap] do
    if h < els.size then
      let x := els[h]!
      for g in [0:gens.size] do
        let y := mulM x gens[g]!
        let k := keyM y
        unless seen.contains k do
          seen := seen.insert k
          els := els.push y
          par := par.push h
          pg := pg.push g
  return (els, par, pg)

@[expose] def indexOf (els : Array (Array Nat)) : Std.HashMap Nat Nat :=
  (List.range els.size).foldl (fun m i => m.insert (keyM els[i]!) i) ∅

@[expose] def look (H : Std.HashMap Nat Nat) (n : Nat) (M : Array Nat) : Nat := H.getD (keyM M) n

@[expose] def rmulT (els gens : Array (Array Nat)) (H : Std.HashMap Nat Nat) :
    Array (Array Nat) :=
  els.map fun x => gens.map fun g => look H els.size (mulM x g)

@[expose] def mulT (R : Array (Array Nat)) (par pg : Array Nat) : Array (Array Nat) :=
  (Array.range par.size).map fun i => Id.run do
    let mut row : Array Nat := #[i]
    for j in [1:par.size] do
      row := row.push R[row[par[j]!]!]![pg[j]!]!
    return row

@[expose] def enumOK (gens els : Array (Array Nat)) (par pg : Array Nat) (H : Std.HashMap Nat Nat)
    (R mt : Array (Array Nat)) (n : Nat) : Bool :=
  els.size == n && par.size == n && pg.size == n && els[0]! == idRows 11 &&
    (List.range n).all (fun i => els[i]!.size == 11 && els[i]!.all (· < 2048)) &&
    (List.range n).all (fun i => look H n els[i]! == i) &&
    (List.range n).all (fun j => j == 0 || (par[j]! < j && pg[j]! < gens.size &&
      els[j]! == mulM els[par[j]!]! gens[pg[j]!]!)) &&
    (List.range n).all (fun i => (List.range gens.size).all fun g =>
      R[i]![g]! < n && els[R[i]![g]!]! == mulM els[i]! gens[g]!) &&
    (List.range n).all (fun i => mt[i]![0]! == i && (List.range n).all fun j =>
      j == 0 || mt[i]![j]! == R[mt[i]![par[j]!]!]![pg[j]!]!)

@[expose] def invsOf (mt : Array (Array Nat)) (n : Nat) : List Nat :=
  (List.range n).filter fun k => k != 0 && mt[k]![k]! == 0

@[expose] def extL (mt : Array (Array Nat)) (L : List Nat) (k : Nat) : List Nat :=
  L ++ L.map fun a => mt[a]![k]!

@[expose] def canExt (mt : Array (Array Nat)) (L : List Nat) (k : Nat) : Bool :=
  !L.contains k && L.all fun a => mt[a]![k]! == mt[k]![a]!

@[expose] def eaList (mt : Array (Array Nat)) (invs : List Nat) (depth : Nat) :
    Array (List Nat) := Id.run do
  let mut all : Array (List Nat) := #[[0]]
  let mut seen : Std.HashSet (List Nat) := (∅ : Std.HashSet (List Nat)).insert [0]
  let mut lvl : Array (List Nat) := #[[0]]
  for _ in [0:depth] do
    let mut nxt : Array (List Nat) := #[]
    for L in lvl do
      for k in invs do
        if canExt mt L k then
          let B := (extL mt L k).mergeSort
          unless seen.contains B do
            seen := seen.insert B
            nxt := nxt.push B
    all := all ++ nxt
    lvl := nxt
  return all

@[expose] def indexL (D : Array (List Nat)) : Std.HashMap (List Nat) Nat :=
  (List.range D.size).foldl (fun m i => m.insert D[i]! i) ∅

@[expose] def eaOK (mt : Array (Array Nat)) (n : Nat) (invs : List Nat) (D : Array (List Nat))
    (HD : Std.HashMap (List Nat) Nat) : Bool :=
  0 < D.size && D[0]! == [0] && D.all (fun L => L.all (· < n)) &&
    D.all fun L => invs.all fun k => !canExt mt L k ||
      (let B := (extL mt L k).mergeSort
       let j := HD.getD B D.size
       j < D.size && D[j]! == B)

@[expose] def fixT (els : Array (Array Nat)) (N : Nat) : Array (Array Bool) :=
  els.map fun M => (Array.range N).map fun x => vecMulN 11 M x == x

@[expose] def fixCount (F : Array (Array Bool)) (N : Nat) (L : List Nat) : Nat :=
  (List.range N).countP fun x => L.all fun i => F[i]![x]!

@[expose] def boundOK (F : Array (Array Bool)) (D : Array (List Nat)) : Bool :=
  D.all fun L => L == [0] || L.length * fixCount F 2048 L ≤ 1024

@[expose] def co1JCheck (Aa Ba : Array Nat) (codes : List (Nat × Nat)) : Bool :=
  let gens := gensOf Aa Ba codes
  let E := enumT gens 1024
  let els := E.1
  let n := els.size
  let H := indexOf els
  let R := rmulT els gens H
  let mt := mulT R E.2.1 E.2.2
  let invs := invsOf mt n
  let D := eaList mt invs 7
  n == 1024 && enumOK gens els E.2.1 E.2.2 H R mt n &&
    (List.range gens.size).all (fun g => vecMulN 11 gens[g]! 3 == 3) &&
    eaOK mt n invs D (indexL D) && boundOK (fixT els 2048) D

end CFSG.KD.Co1K105
