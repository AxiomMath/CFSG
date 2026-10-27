module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.OddStandard.ONanRec.A6C

open CFSG.QuasithinUnique.A6Facts.Core

@[expose] def ord4 (u : List Nat) : Bool := cpow u 4 == cid && !(cpow u 2 == cid)

@[expose] def pCond (u r : List Nat) : Bool :=
  !(r == cid) && cpow r 3 == cid &&
    cmul (cmul (cmul u r) (cpow u 3)) r == cmul r (cmul (cmul u r) (cpow u 3)) &&
    cmul (cmul (cpow u 2) r) (cpow u 2) == cpow r 2

@[expose] def dCond (u d : List Nat) : Bool :=
  cpow d 2 == cid && !(d == cid) && cmul (cmul (cmul d u) d) u == cid

@[expose] def pElt (u r0 : List Nat) (i j : Nat) : List Nat :=
  cmul (cpow r0 i) (cpow (cmul (cmul u r0) (cpow u 3)) j)

@[expose] def eOf (u r : List Nat) : List Nat := cmul (cmul r (cpow u 2)) (cpow r 2)

@[expose] def conjPow (b : List Nat) (k : Nat) (x : List Nat) : List Nat :=
  cmul (cmul (cpow b k) x) (cpow (cpow b 119) k)

@[expose] def relG (b d e : List Nat) : Bool :=
  cmul (cmul (cmul (conjPow b 3 (cmul e d)) (conjPow b 2 (cmul d e))) (conjPow b 1 (cmul e d)))
    d == cid

@[expose] def bCond (u d b : List Nat) : Bool :=
  cmul b u == cmul (cpow u 3) b && cmul b d == cmul (cmul u d) b &&
    pslGenC.all fun x =>
      cmul (cpow b 2) x == cmul (cmul (cmul (cpow u 2) x) (cpow u 2)) (cpow b 2)

@[expose] def a6ExpCheck : Bool := autL.all fun b => cpow b 120 == cid

@[expose] def a6OrdCheck : Bool :=
  pslLit.all fun x => (!(cpow x 6 == cid) || cpow x 2 == cid || cpow x 3 == cid) &&
    (!(cpow x 8 == cid) || cpow x 4 == cid)

@[expose] def a6SylCheck : Bool := pslLit.all fun u => !ord4 u || pslLit.any fun r => pCond u r

@[expose] def a6DistCheck : Bool :=
  pslLit.all fun u => !ord4 u || pslLit.all fun r => !pCond u r ||
    decide (((List.range 3).flatMap fun i => (List.range 3).map fun j => pElt u r i j).Nodup)

@[expose] def a6InvCheck : Bool := pslLit.all fun u => !ord4 u || pslLit.any fun w => dCond u w

@[expose] def a6FixCheck : Bool :=
  autL.all fun b => b == cid || pslLit.all fun u => !(ord4 u && cmul b u == cmul u b) ||
    pslLit.all fun r => !(pCond u r && cmul b r == cmul r b)

@[expose] def a6RelCheck : Bool :=
  pslLit.all fun u => !ord4 u || pslLit.all fun d => !dCond u d ||
    ((pslLit.all fun r0 => !pCond u r0 || (List.range 3).any fun i => (List.range 3).any fun j =>
        cpow (cmul d (eOf u (pElt u r0 i j))) 3 == cid) &&
      autL.all fun b => !bCond u d b || pslLit.all fun r0 => !pCond u r0 ||
        (List.range 3).all fun i => (List.range 3).all fun j =>
          !(cpow (cmul d (eOf u (pElt u r0 i j))) 3 == cid) ||
            relG b d (eOf u (pElt u r0 i j)) ||
            relG (cmul (cpow u 2) b) d (eOf u (pElt u r0 i j)))

@[expose] def a6MirrorCheck : Bool :=
  a6ExpCheck && a6OrdCheck && a6SylCheck && a6DistCheck && a6InvCheck && a6FixCheck &&
    a6RelCheck

end CFSG.OddStandard.ONanRec.A6C
