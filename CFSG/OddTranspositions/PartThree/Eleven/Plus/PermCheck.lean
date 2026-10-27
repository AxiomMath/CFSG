module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermData

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def plusTableSizeCheck (_ : Unit := ()) : Bool :=
  (plusTable.size == 60) && allLt 60 fun i => (plusTable[i]!).size == 60

@[expose] def plusTableValidCheck (_ : Unit := ()) : Bool :=
  allLt 60 fun i => validA 60 plusTable[i]!

@[expose] def plusTableInvolCheck (_ : Unit := ()) : Bool :=
  allLt 60 fun i => allLt 60 fun j => (plusTable[i]!)[(plusTable[i]!)[j]!]! == j

@[expose] def plusTableConjCheck (_ : Unit := ()) : Bool :=
  allLt 60 fun i => allLt 60 fun j =>
    eqA 60 plusTable[(plusTable[i]!)[j]!]!
      (compA 60 plusTable[i]! (compA 60 plusTable[j]! plusTable[i]!))

@[expose] def plusTableKeyCheck (_ : Unit := ()) : Bool :=
  allLt 60 fun i => allLt 60 fun j =>
    (keyA 60 plusBase plusTable[i]! == keyA 60 plusBase plusTable[j]!) == (i == j)

@[expose] def plusTableCheck (_ : Unit := ()) : Bool :=
  plusTableSizeCheck () && plusTableValidCheck () && plusTableInvolCheck () &&
    plusTableConjCheck () && plusTableKeyCheck ()

@[expose] def plusEnumCheck (_ : Unit := ()) : Bool :=
  let E := plusEnum ()
  enumOK 60 plusTable plusBase E && (E.pts.size == 7200)

end CFSG.OddTranspositions.PartThree
