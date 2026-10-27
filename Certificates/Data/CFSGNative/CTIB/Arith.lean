module

public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import Std.Data.HashMap

public section

namespace CFSG.Monster.B.CTIB.Native

open CFSG.Monster.B.Max2.Native (act22)

@[expose] def cAtN (gj u j : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => cAtN gj u j n ^^ (decide (j < n) && u.testBit n && gj.testBit n)

@[expose] def cAt (G : Array Nat) (u j : Nat) : Bool := cAtN (G.getD j 0) u j 22

@[expose] def corrN (G : Array Nat) (a b : Nat) : Nat → Bool
  | 0 => false
  | m + 1 => if b.testBit m then corrN G a b m ^^ cAt G a m else corrN G a b m

@[expose] def corr (G : Array Nat) (a b : Nat) : Bool := corrN G a b 22

@[expose] def qmul (G : Array Nat) (a b : Nat) : Nat :=
  (a ^^^ b) % 2 ^ 22 ||| (if (a.testBit 22 ^^ b.testBit 22) ^^ corr G a b then 2 ^ 22 else 0)

@[expose] def autApplyN (G A : Array Nat) (n : Nat) : Nat → Nat
  | 0 => if n.testBit 22 then 2 ^ 22 else 0
  | m + 1 => if n.testBit m then qmul G (autApplyN G A n m) (A.getD m 0) else autApplyN G A n m

@[expose] def autApply (G A : Array Nat) (n : Nat) : Nat := autApplyN G A n 22

@[expose] def id23 (_ : Unit := ()) : Array Nat := ((List.range 22).map (2 ^ ·)).toArray

@[expose] def autComp (G A B : Array Nat) : Array Nat := A.map (autApply G B)

@[expose] def autPow (G A : Array Nat) : Nat → Array Nat
  | 0 => id23
  | k + 1 => autComp G (autPow G A k) A

@[expose] def autWord (G : Array Nat) (tab : Nat → Array Nat) (w : List Nat) : Array Nat :=
  w.foldl (fun A l => autComp G A (tab l)) id23

@[expose] def signedImg (rows : List Nat) (signs i : Nat) : Nat :=
  rows.getD i 0 ||| (if signs.testBit i then 2 ^ 22 else 0)

@[expose] def isInv (G A : Array Nat) (w n : Nat) : Bool :=
  qmul G w (qmul G (autApply G A n) n) == 0

@[expose] def isInvF (G A L : Array Nat) (w n : Nat) : Bool :=
  act22 L (n % 2 ^ 22) == n % 2 ^ 22 && isInv G A w n

@[specialize, expose] def countBelow (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | m + 1, acc => countBelow p m (if p m then acc + 1 else acc)

@[expose] def countInv (G A L : Array Nat) (w : Nat) : Nat :=
  countBelow (isInvF G A L w) (2 ^ 23) 0

@[expose] def qconj (G A : Array Nat) (k n : Nat) : Nat :=
  qmul G (A.getD k 0) (qmul G n (2 ^ k))

@[expose] def fuse (G A : Array Nat) (d n : Nat) : Nat := qmul G d (autApply G A n)

@[expose] def natPointOK (act : Nat → Nat → Nat) (ngen : Nat) (valid : Nat → Bool)
    (pts : Array Nat) (edges : Array (Array Nat)) (par lab : Array Nat) (i : Nat) : Bool :=
  valid pts[i]! && (edges[i]!).size == ngen &&
    (List.range ngen).all (fun k => decide (edges[i]![k]! < pts.size) &&
      pts[edges[i]![k]!]! == act k pts[i]!) &&
    (i == 0 || (decide (par[i]! < i) && decide (lab[i]! < ngen) &&
      pts[i]! == act lab[i]! pts[par[i]!]!))

@[expose] def chainLt : List Nat → Bool
  | a :: b :: t => decide (a < b) && chainLt (b :: t)
  | _ => true

@[expose] def natCertOK (act : Nat → Nat → Nat) (ngen : Nat) (valid : Nat → Bool) (root : Nat)
    (pts : Array Nat) (edges : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  decide (0 < pts.size) && pts[0]! == root &&
    (List.range pts.size).all (natPointOK act ngen valid pts edges par lab) &&
    chainLt (pts.toList.mergeSort (fun a b => decide (a ≤ b)))

@[expose] def natBfs (act : Nat → Nat → Nat) (ngen : Nat) (root : Nat) (fuel : Nat) :
    Array Nat × Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut idx : Std.HashMap Nat Nat := (∅ : Std.HashMap Nat Nat).insert root 0
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut edges : Array (Array Nat) := #[]
  for i in [0:fuel] do
    if i < pts.size then
      let p := pts[i]!
      let mut row : Array Nat := Array.mkEmpty ngen
      for k in [0:ngen] do
        let y := act k p
        match idx.get? y with
        | some j => row := row.push j
        | none =>
          idx := idx.insert y pts.size
          row := row.push pts.size
          pts := pts.push y
          par := par.push i
          lab := lab.push k
      edges := edges.push row
  return (pts, edges, par, lab)

@[expose] def orbitOK (act : Nat → Nat → Nat) (ngen : Nat) (valid : Nat → Bool)
    (root size : Nat) : Bool :=
  let c := natBfs act ngen root (size + 1)
  natCertOK act ngen valid root c.1 c.2.1 c.2.2.1 c.2.2.2 && c.1.size == size &&
    c.1.all (root ≤ ·)

@[expose] def parseNats (s : String) : List Nat := (s.splitOn " ").filterMap String.toNat?

@[expose] def letterOf (c : Char) : Int :=
  if c = 'a' then 1 else if c = 'b' then 2 else if c = 'c' then 3
  else if c = 'A' then -1 else if c = 'B' then -2 else if c = 'C' then -3 else 0

@[expose] def parseWords (s : String) : List (List Int) :=
  (s.splitOn " ").map fun w => w.toList.map letterOf

end CFSG.Monster.B.CTIB.Native
