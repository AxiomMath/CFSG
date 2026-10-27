module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3

public section

namespace CFSG.RankThree.PartTwo.J2Residue.C16

open CFSG.ComponentClassification.J2Cover.Models CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (zArr)

@[expose] def x0Word : List Nat :=
  [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1,
    1, 0, 1, 1, 0, 1, 0, 1, 0]

@[expose] def cWord : List Nat :=
  [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0,
    1]

@[expose] def d0 : List Nat := [0, 4, 81, 85, 88, 94, 115, 124]

@[expose] def lamMaskD0 : Nat := 2 ^ 4 + 2 ^ 94 + 2 ^ 115

@[expose] def c16Check (_ : Unit := ()) : Bool :=
  let x0 := wordArr x0Word
  let c := wordArr cWord
  eqA 315 (compA 315 c zArr) (compA 315 x0 c) &&
  d0.all (fun a => d0.contains invTab[a]! && d0.all fun b => d0.contains mulTab[a]![b]!) &&
  d0.all (fun a => eqA 315 (compA 315 eltArrs[a]! x0) (compA 315 x0 eltArrs[a]!)) &&
  !(maskBit lamMaskD0 0) &&
  d0.all (fun a => d0.all fun b => bitAt fRows a b == cobBit lamMaskD0 a b)

end CFSG.RankThree.PartTwo.J2Residue.C16
