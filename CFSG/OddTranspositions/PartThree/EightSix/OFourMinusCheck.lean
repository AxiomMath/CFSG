module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermData
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def minusTripleArr (i k j : ℕ) : Array ℕ :=
  compA 65 (compA 65 minusTable[i]! minusTable[k]!) minusTable[j]!

@[expose] def minusTripleSq (i k j : ℕ) : Array ℕ :=
  let p := minusTripleArr i k j
  compA 65 p p

@[expose] def minusTripleFourth (i k j : ℕ) : Array ℕ :=
  let p := minusTripleSq i k j
  compA 65 p p

@[expose] def minusPairArr (i j : ℕ) : Array ℕ :=
  compA 65 minusTable[i]! minusTable[j]!

@[expose] def minusPairCube (i j : ℕ) : Array ℕ :=
  let a := minusPairArr i j
  compA 65 (compA 65 a a) a

@[expose] def minusSecondKindCheck (_ : Unit := ()) : Bool :=
  let I := idA 65
  allLt 65 fun i => allLt 65 fun k => allLt 65 fun j =>
    if i == k then true
    else if (minusTable[i]!)[k]! == k then
      if (minusTable[i]!)[j]! == j then true
      else if (minusTable[k]!)[j]! == j then true
      else
        let p4 := minusTripleFourth i k j
        let p2 := minusTripleSq i k j
        if eqA 65 p4 I && !eqA 65 p2 I then
          let a3 := minusPairCube i j
          let b3 := minusPairCube k j
          eqA 65 a3 I && eqA 65 b3 I
        else true
    else true

end CFSG.OddTranspositions.PartThree
