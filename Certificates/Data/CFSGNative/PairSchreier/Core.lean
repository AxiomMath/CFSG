module

public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Schreier.PairNative

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[inline, expose] def evR (w : List (Array Nat)) (p : Nat) : Nat :=
  w.foldl (fun q t => t[q]!) p

@[expose] def evPow (w : List (Array Nat)) : Nat → Nat → Nat
  | 0, p => p
  | e + 1, p => evR w (evPow w e p)

@[expose] def fixB (bs : List Nat) (w : List (Array Nat)) (e : Nat) : Bool :=
  bs.all fun b => evPow w e b == b

@[expose] def ordB (bs : List Nat) (w : List (Array Nat)) (m : Nat) : Bool :=
  fixB bs w m && (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => !fixB bs w e

@[expose] def patW (x y : List (Array Nat)) (pat : List Bool) : List (Array Nat) :=
  (pat.reverse.map fun b => if b then y else x).flatten

@[expose] def condsOK (bs : List Nat) (x y : List (Array Nat)) (conds : List (List Bool × Nat)) :
    Bool :=
  conds.all fun c => ordB bs (patW x y c.1) c.2

@[expose] def countW (f : List (Array Nat) → Bool) :
    List (Array (Array Nat)) → List (Array Nat) → Nat
  | [], acc => if f acc then 1 else 0
  | B :: Bs, acc => B.foldl (fun c t => c + countW f Bs (t :: acc)) 0

@[expose] def chunksOf {α : Type} (sz : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, a :: l => (a :: l).take sz :: chunksOf sz fuel ((a :: l).drop sz)

@[expose] def countWPar (sz : Nat) (f : List (Array Nat) → Bool) (B : Array (Array Nat))
    (Bs : List (Array (Array Nat))) : Nat :=
  ((chunksOf sz B.size B.toList).map fun piece =>
    Task.spawn fun _ => piece.foldl (fun c t => c + countW f Bs [t]) 0).foldl
      (fun c t => c + t.get) 0

@[expose] def blockOf (n : Nat) : List (Array (Array Nat)) → Array (Array Nat)
  | [] => #[idA n]
  | L :: Ls =>
    let R := blockOf n Ls
    L.foldl (fun acc t => R.foldl (fun acc r => acc.push (compA n t r)) acc) #[]

@[expose] def levelArr (L : Array Level) (i : Nat) : Array (Array Nat) :=
  Array.ofFn (n := L[i]!.pts.size) fun k => L[i]!.tr[k.val]!

@[expose] def blocksOf (n : Nat) (L : Array Level) (groups : List (List Nat)) :
    List (Array (Array Nat)) :=
  groups.map fun g => blockOf n (g.map (levelArr L))

@[expose] def nfWord (L : Array Level) (nf : Array Nat) : List (Array Nat) :=
  (List.range nf.size).reverse.map fun i => L[i]!.tr[nf[i]!]!

@[expose] def nfOK (L : Array Level) (nf : Array Nat) : Bool :=
  nf.size == L.size && allLt nf.size fun i => decide (nf[i]! < L[i]!.pts.size)

@[expose] def baseImgs (bs : List Nat) (w : List (Array Nat)) : List Nat := bs.map (evR w)

@[expose] def conjImgs (bs : List Nat) (g gi : Array Nat) (w : List (Array Nat)) : List Nat :=
  bs.map fun b => g[evR w gi[b]!]!

@[expose] def decodeNF (L : Array Level) (imgs : Array Nat) : Array Nat := Id.run do
  let mut cur := imgs
  let mut nf : Array Nat := #[]
  for i in [0:L.size] do
    let k := L[i]!.pos[cur[i]!]!
    nf := nf.push k
    let ti := L[i]!.trInv[k]!
    cur := cur.map fun x => ti[x]!
  return nf

@[expose] def imgKey (n : Nat) (imgs : List Nat) : Nat := imgs.foldr (fun x acc => x + n * acc) 0

@[expose] def conjClosureNF (n : Nat) (L : Array Level) (bs : List Nat)
    (gens gensInv : Array (Array Nat)) (nf₀ : Array Nat) (cap : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashSet Nat :=
    (∅ : Std.HashSet Nat).insert (imgKey n (baseImgs bs (nfWord L nf₀)))
  let mut elts : Array (Array Nat) := #[nf₀]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let w := nfWord L elts[h]!
      for l in [0:gens.size] do
        let imgs := conjImgs bs gens[l]! gensInv[l]! w
        let kz := imgKey n imgs
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push (decodeNF L imgs.toArray)
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def allFrom (a b : Nat) (p : Nat → Bool) : Bool := allLt b fun k => decide (k < a) || p k

@[expose] def closureOK (L : Array Level) (bs : List Nat) (gens gensInv : Array (Array Nat))
    (rep : List (Array Nat)) (elts : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  decide (0 < elts.size) && allLt elts.size (fun k => nfOK L elts[k]!) &&
    baseImgs bs (nfWord L elts[0]!) == baseImgs bs rep &&
    allFrom 1 elts.size fun k => decide (par[k]! < k) && decide (lab[k]! < gens.size) &&
      baseImgs bs (nfWord L elts[k]!) ==
        conjImgs bs gens[lab[k]!]! gensInv[lab[k]!]! (nfWord L elts[par[k]!]!)

@[expose] def strictInc : List Nat → Bool
  | a :: b :: l => decide (a < b) && strictInc (b :: l)
  | _ => true

@[expose] def keysDistinctNF (n : Nat) (L : Array Level) (bs : List Nat)
    (cl : List (Array (Array Nat))) : Bool :=
  strictInc ((cl.flatMap fun c =>
    c.toList.map fun nf => imgKey n (baseImgs bs (nfWord L nf))).mergeSort)

end CFSG.Sporadic.Schreier.PairNative
