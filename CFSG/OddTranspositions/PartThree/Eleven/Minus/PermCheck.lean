module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermData

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def minusTableSizeCheck (_ : Unit := ()) : Bool :=
  (minusTable.size == 65) && allLt 65 fun i => (minusTable[i]!).size == 65

@[expose] def minusTableValidCheck (_ : Unit := ()) : Bool :=
  allLt 65 fun i => validA 65 minusTable[i]!

@[expose] def minusTableInvolCheck (_ : Unit := ()) : Bool :=
  allLt 65 fun i => allLt 65 fun j => (minusTable[i]!)[(minusTable[i]!)[j]!]! == j

@[expose] def minusTableConjCheck (_ : Unit := ()) : Bool :=
  allLt 65 fun i => allLt 65 fun j =>
    eqA 65 minusTable[(minusTable[i]!)[j]!]!
      (compA 65 minusTable[i]! (compA 65 minusTable[j]! minusTable[i]!))

@[expose] def minusTableKeyCheck (_ : Unit := ()) : Bool :=
  allLt 65 fun i => allLt 65 fun j =>
    (keyA 65 minusBase minusTable[i]! == keyA 65 minusBase minusTable[j]!) == (i == j)

@[expose] def minusTableCheck (_ : Unit := ()) : Bool :=
  minusTableSizeCheck () && minusTableValidCheck () && minusTableInvolCheck () &&
    minusTableConjCheck () && minusTableKeyCheck ()

@[expose] def minusEnumCheck (_ : Unit := ()) : Bool :=
  let E := minusEnum ()
  enumOK 65 minusTable minusBase E && (E.pts.size == 15600)

end CFSG.OddTranspositions.PartThree
