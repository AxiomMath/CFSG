
module

public import CFSG.Sporadic.Co1.Module.OddChecksInputs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

def type2Pts : Array ℕ := (orbitOf 2 98280).pts

def type2Pos : Array UInt32 := posTable 24 type2Pts

def isT2 (x : ℕ) : Bool :=
  inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x

def isT4' (x : ℕ) : Bool :=
  type4N (transposeRows 24 qRows) (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 x

def vecsOne : List ℕ := Wk 1

def vecsTwo : List ℕ := Wk 2

def noTwoOK : Bool := vecsOne.all fun x => !isT2 x

def disjOK : Bool :=
  distinctKeys (((FZ 1).pts ++ FS.pts).toList.map rowsKey)

def zsTwo : Array (Array ℕ) := (FZ 2).pts

def zsTwoList : List (Array ℕ) := zsTwo.toList

def f4List : List ℕ := vecsTwo.filter isT4'

def w2List : List ℕ := vecsTwo.filter isT2

def yList : List ℕ := w2List.filter fun u => isT2 (u ^^^ code4)

def coverOK : Bool := w2List.all fun u => f4List.any fun ω => isT2 (u ^^^ ω)

def orbitOK (Zs : List (Array ℕ)) (L : List ℕ) : Bool :=
  match L with
  | [] => false
  | u₀ :: _ => L.all fun u => Zs.any fun z => vecMulN 24 (transposeRows 24 z) u₀ == u

def orbitYOK : Bool := orbitOK zsTwoList yList

def tripleOK : Bool := w2List.any fun u₁ => w2List.any fun u₂ => isT4' (u₁ ^^^ u₂)

def existsBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => p n || existsBelow p n

def fsList : List (Array ℕ) := FS.pts.toList

def outerTest (y : Array ℕ) (u : ℕ) : Bool :=
  isFixedN (Mt 27) (vecMulN 24 (transposeRows 24 y) u ^^^ u) &&
    isFixedN (Mt (sIdx[2]!)) (vecMulN 24 (transposeRows 24 y) u ^^^ u) &&
    isT4' (vecMulN 24 (transposeRows 24 y) u ^^^ u)

def outerOK : Bool :=
  zsTwoList.all fun y => !(fsList.contains y) || existsBelow (outerTest y) 16777216

end CFSG.Sporadic.Co1.Module.Odd
