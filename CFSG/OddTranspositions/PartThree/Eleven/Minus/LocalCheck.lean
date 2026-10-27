module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def minusLocalValid (_ : Unit := ()) : Bool :=
  validA 65 minusTable[0]! && validA 65 minusSylowA && validA 65 minusSylowB &&
    validA 65 minusA5Gens[0]! && validA 65 minusA5Gens[1]!

@[expose] def minusSylowAOrder (_ : Unit := ()) : Bool :=
  eqA 65 (compA 65 (compA 65 minusSylowA minusSylowA) (compA 65 minusSylowA minusSylowA))
      (idA 65) &&
    (eqA 65 (compA 65 minusSylowA minusSylowA) (idA 65) == false)

@[expose] def minusSylowBSq (_ : Unit := ()) : Bool :=
  eqA 65 (compA 65 minusSylowB minusSylowB) (idA 65)

@[expose] def minusSylowConj (_ : Unit := ()) : Bool :=
  eqA 65 (compA 65 (compA 65 minusSylowB minusSylowA) minusSylowB)
    (compA 65 (compA 65 minusSylowA minusSylowA) minusSylowA)

@[expose] def minusSylowNotMem (_ : Unit := ()) : Bool :=
  (eqA 65 minusSylowB (idA 65) == false) &&
    (eqA 65 minusSylowB minusSylowA == false) &&
    (eqA 65 minusSylowB (compA 65 minusSylowA minusSylowA) == false) &&
    (eqA 65 minusSylowB (compA 65 (compA 65 minusSylowA minusSylowA) minusSylowA) == false)

@[expose] def minusA5Commute (_ : Unit := ()) : Bool :=
  allLt minusA5Gens.size fun k =>
    eqA 65 (compA 65 minusA5Gens[k]! minusTable[0]!)
      (compA 65 minusTable[0]! minusA5Gens[k]!)

@[expose] def minusA5EnumOK (_ : Unit := ()) : Bool :=
  let c := minusA5Enum ()
  enumOK 65 minusA5Gens minusBase c && (c.pts.size == 60)

@[expose] def minusA5Simple (_ : Unit := ()) : Bool :=
  conjSimpleOK 65 minusBase (minusA5Enum ())

@[expose] def minusLocalCheck (_ : Unit := ()) : Bool :=
  ((minusLocalValid () && minusSylowAOrder ()) && (minusSylowBSq () && minusSylowConj ())) &&
    ((minusSylowNotMem () && minusA5Commute ()) && (minusA5EnumOK () && minusA5Simple ()))

end CFSG.OddTranspositions.PartThree
