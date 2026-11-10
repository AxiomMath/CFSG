module

public import CFSG.Sporadic.Co1.Module.InvDataInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Pairs

open CFSG.Blueprint MulAction CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative

def invWordL (w : List Bool) : List Bool :=
  w.reverse.flatMap fun b => if b then [true] else [false, false]

def conjRows (w : List Bool) : Array ℕ :=
  mulRows 24 rowsSA (mulRows 24 (mulRows 24 (wordRows w) rowsSA) (wordRows (invWordL w)))

def rootW1 : List Bool := invWord "BBBABA"

def rootW2 : List Bool := invWord "ABABAA"

def rootRows1 : Array ℕ := powRows 24 (conjRows rootW1) 3

def rootRows2 : Array ℕ :=
  mulRows 24 (wordRows (invWordL rootW2)) (powRows 24 (conjRows rootW2) 2)

def rootBase : ℕ := 16181251

def rootFix : List ℕ :=
  [11665409, 2, 3342340, 3276808, 3342352, 8454176, 3473472, 196736, 1114368, 11534848,
    14287872, 13568000, 8982528, 13836288, 8404992, 14188544]

def dualCode (c : ℕ) : ℕ := vecMulN 24 (transposeRows 24 f0Rows) c

def rootGs : List ℕ := rootFix.map dualCode

def orthAll (gs : List ℕ) (u : ℕ) : Bool := gs.all fun g => !parity24 (u &&& g)

def coverOK (O : VOrbit) (gs : List ℕ) (L : Array ℕ) : Bool :=
  (List.range 98280).all fun p => !orthAll gs O.pts[p]! || L.contains O.pts[p]!

def rootCheckT (O : VOrbit) (f : ℕ → ℕ → ℕ) (L par lab : Array ℕ) : Bool :=
  mulRows 24 rootRows1 rowsSA == mulRows 24 rowsSA rootRows1 &&
  mulRows 24 rootRows2 rowsSA == mulRows 24 rowsSA rootRows2 &&
  rootFix.all (fun c => decide (c < 2 ^ 24) && isFixedN (transposeRows 24 rowsSA) c) &&
  treeCheckV f L par lab && coverOK O rootGs L

def rootCheck : Bool :=
  rootCheckT (orbitOf 2 98280) (mclAct rootRows1 rootRows2)
    (bfsTree (mclAct rootRows1 rootRows2) rootBase 400).1
    (bfsTree (mclAct rootRows1 rootRows2) rootBase 400).2.1
    (bfsTree (mclAct rootRows1 rootRows2) rootBase 400).2.2

end CFSG.Sporadic.Co1.Module.Pairs
