module

public import Certificates.Data.CFSGNative.HS.SmallF2
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Co1.OddNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def lineRows (regs : Array (Array Nat)) (fac : List (Nat × Nat)) : Array Nat :=
  fac.foldl (fun acc p => mulRows 24 acc (powRows 24 (regs[p.1]?.getD (idRows 24)) p.2))
    (idRows 24)

@[expose] def runRows (init : Array (Array Nat)) (prog : List (List (Nat × Nat))) :
    Array (Array Nat) :=
  prog.foldl (fun regs fac => regs.push (lineRows regs fac)) init

@[expose] def rowsKey (x : Array Nat) : Nat := x.toList.foldr (fun r acc => r + 16777216 * acc) 0

@[expose] def validRows (x : Array Nat) : Bool :=
  x.size == 24 && x.all fun r => decide (r < 16777216)

@[expose] def keyLe (a b : Nat) : Bool := decide (a ≤ b)

@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a < b) && strictInc (b :: t)

@[expose] def distinctKeys (keys : List Nat) : Bool := strictInc (keys.mergeSort keyLe)

structure Forest where
  pts : Array (Array Nat)
  par : Array Nat
  lab : Array Nat
  rt : Array Nat
deriving Inhabited

@[expose] def stepRows (P Q : Array (Array Nat)) (l : Nat) (x : Array Nat) : Array Nat :=
  mulRows 24 (mulRows 24 P[l]! x) Q[l]!

@[expose] def forestPointOK (P Q roots : Array (Array Nat)) (F : Forest) (i : Nat) : Bool :=
  validRows F.pts[i]! &&
    (if i < roots.size then F.pts[i]! == roots[i]! && F.rt[i]! == i
     else decide (F.par[i]! < i) && decide (F.lab[i]! < P.size) && decide (F.lab[i]! < Q.size) &&
       F.rt[i]! == F.rt[F.par[i]!]! && F.pts[i]! == stepRows P Q F.lab[i]! F.pts[F.par[i]!]!)

@[expose] def forestOK (P Q roots : Array (Array Nat)) (F : Forest) : Bool :=
  decide (roots.size ≤ F.pts.size) && F.par.size == F.pts.size && F.lab.size == F.pts.size &&
    F.rt.size == F.pts.size && (List.range F.pts.size).all (forestPointOK P Q roots F) &&
    distinctKeys (F.pts.toList.map rowsKey)

def forestBFS (P Q roots : Array (Array Nat)) (cap : Nat) : Forest :=
  Id.run do
    let mut pts : Array (Array Nat) := roots
    let mut par : Array Nat := Array.range roots.size
    let mut lab : Array Nat := Array.replicate roots.size 0
    let mut rt : Array Nat := Array.range roots.size
    let mut seen : Std.HashSet (Array Nat) := {}
    for r in roots do
      seen := seen.insert r
    let mut h := 0
    while h < pts.size && pts.size < cap do
      for l in [0:P.size] do
        let y := stepRows P Q l pts[h]!
        if !seen.contains y then
          seen := seen.insert y
          pts := pts.push y
          par := par.push h
          lab := lab.push l
          rt := rt.push rt[h]!
      h := h + 1
    return ⟨pts, par, lab, rt⟩

@[expose] def countBelow (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => countBelow p n (if p n then acc + 1 else acc)

@[expose] def collectBelow (p : Nat → Bool) : Nat → List Nat → List Nat
  | 0, acc => acc
  | n + 1, acc => collectBelow p n (if p n then n :: acc else acc)

@[expose] def rtCount (F : Forest) (j : Nat) : Nat :=
  countBelow (fun i => F.rt[i]! == j) F.rt.size 0

@[expose] def isFixedN (Mt : Array Nat) (x : Nat) : Bool := vecMulN 24 Mt x == x

@[expose] def dotN (x y : Nat) : Bool :=
  (List.range 24).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) false

@[expose] def q0N (Qt : Array Nat) (x : Nat) : Bool := dotN x (vecMulN 24 Qt x)

@[expose] def inPts (pts : Array Nat) (pos : Array UInt32) (n w : Nat) : Bool :=
  decide ((pos[w]!).toNat < n) && pts[(pos[w]!).toNat]! == w

@[expose] def type4N (Qt : Array Nat) (pts : Array Nat) (pos : Array UInt32) (n x : Nat) : Bool :=
  x != 0 && !q0N Qt x && !inPts pts pos n x

@[expose] def fixCount (Ms : List (Array Nat)) : Nat :=
  countBelow (fun x => Ms.all fun Mt => isFixedN Mt x) 16777216 0

@[expose] def fixCount4 (Ms : List (Array Nat)) (Qt pts : Array Nat) (pos : Array UInt32)
    (n : Nat) : Nat :=
  countBelow (fun x => (Ms.all fun Mt => isFixedN Mt x) && type4N Qt pts pos n x) 16777216 0

@[expose] def fixList (Ms : List (Array Nat)) : List Nat :=
  collectBelow (fun x => Ms.all fun Mt => isFixedN Mt x) 16777216 []

@[expose] def bilN (Ft : Array Nat) (u v : Nat) : Bool := dotN u (vecMulN 24 Ft v)

@[expose] def gramOK (Ft : Array Nat) (W : List Nat) : Bool :=
  W.all fun u => u == 0 || W.any fun v => bilN Ft u v

@[expose] def faithfulOK (Zs : Array (Array Nat)) (W : List Nat) : Bool :=
  Zs.all fun z => z == idRows 24 || W.any fun v => !isFixedN (transposeRows 24 z) v

@[expose] def orderLoop (M : Array Nat) : Nat → Array Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, cur, m => if cur == idRows 24 then m else orderLoop M fuel (mulRows 24 cur M) (m + 1)

@[expose] def orderN (M : Array Nat) : Nat := orderLoop M 400 M 1

@[expose] def ordersWith (rho : Array Nat) (F : Forest) : Array Nat :=
  F.pts.map fun x => orderN (mulRows 24 rho x)

@[expose] def oddCount (ords : Array Nat) : Nat :=
  countBelow (fun i => ords[i]! % 2 == 1 && ords[i]! != 1) ords.size 0

@[expose] def zeroCount (ords : Array Nat) : Nat :=
  countBelow (fun i => ords[i]! == 0) ords.size 0

end CFSG.Sporadic.Co1.OddNative
