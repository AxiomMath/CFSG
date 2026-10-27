module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co1.InvNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def genWordRows (G : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldl (fun acc l => mulRows 24 acc G[l]!) (idRows 24)

@[expose] def invRowsLoop (M : Array Nat) : Nat → Array Nat → Array Nat
  | 0, _ => idRows 24
  | fuel + 1, cur =>
    let next := mulRows 24 cur M
    if next == idRows 24 then cur else invRowsLoop M fuel next

@[expose] def invRows (M : Array Nat) : Array Nat := invRowsLoop M 100000 M

@[expose] def countBelow (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countBelow p n (if p n then acc + 1 else acc)

@[expose] def isFixedN (Mt : Array Nat) (x : Nat) : Bool := vecMulN 24 Mt x == x

@[expose] def dotN (x y : Nat) : Bool :=
  (List.range 24).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false

@[expose] def q0N (Qt : Array Nat) (x : Nat) : Bool := dotN x (vecMulN 24 Qt x)

@[expose] def fixCount (Mt : Array Nat) : Nat := countBelow (isFixedN Mt) 16777216 0

@[expose] def fixCountQ (Mt Qt : Array Nat) : Nat :=
  countBelow (fun x => isFixedN Mt x && q0N Qt x) 16777216 0

@[expose] def conjRows (g gi x : Array Nat) : Array Nat := mulRows 24 (mulRows 24 g x) gi

@[expose] def rowsKey (x : Array Nat) : Nat := x.toList.foldr (fun r acc => r + 16777216 * acc) 0

@[expose] def validRows (x : Array Nat) : Bool :=
  x.size == 24 && x.all fun r => decide (r < 16777216)

@[expose] def keyLe (a b : Nat) : Bool := decide (a ≤ b)

@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && strictInc (b :: t)

@[expose] def distinctKeys (keys : List Nat) : Bool := strictInc (keys.mergeSort keyLe)

structure ConjCert where
  pts : Array (Array Nat)
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def ctPointOK (G Gi : Array (Array Nat)) (c : ConjCert) (i : Nat) : Bool :=
  validRows c.pts[i]! &&
    (i == 0 || (decide (c.par[i]! < i) && decide (c.lab[i]! < G.size) &&
      c.pts[i]! == conjRows G[c.lab[i]!]! Gi[c.lab[i]!]! c.pts[c.par[i]!]!))

@[expose] def ctOK (G Gi : Array (Array Nat)) (root : Array Nat) (c : ConjCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    allIn 0 c.pts.size (ctPointOK G Gi c) && distinctKeys (c.pts.toList.map rowsKey)

def conjBFS (G Gi : Array (Array Nat)) (root : Array Nat) (cap : Nat) : ConjCert :=
  Id.run do
    let mut pts : Array (Array Nat) := #[root]
    let mut par : Array Nat := #[0]
    let mut lab : Array Nat := #[0]
    let mut idx : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert (rowsKey root) 0
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:G.size] do
        let y := conjRows G[l]! Gi[l]! pts[h]!
        let k := rowsKey y
        if !idx.contains k then
          idx := idx.insert k pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    return ⟨pts, par, lab⟩

@[expose] def neqId (R : Array Nat) : Bool :=
  (List.range 24).any fun i => (List.range 24).any fun j =>
    (R[i]?.getD 0).testBit j != decide (i = j)

@[expose] def orderIs (M : Array Nat) (n : Nat) : Bool :=
  powRows 24 M n == idRows 24 &&
    (List.range n).all fun m => decide (m = 0) || neqId (powRows 24 M m)

end CFSG.Sporadic.Co1.InvNative
