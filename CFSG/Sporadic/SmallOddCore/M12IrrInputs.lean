module

public import CFSG.Sporadic.SmallOddCore.IrrSylowCheck
public meta import CFSG.Sporadic.SmallOddCore.IrrSylowCheck

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native

@[expose] def m12A1Tbl : Table :=
  #[3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5, 15, 13, 21, 12, 22, 23, 18, 19, 20, 14, 16, 17]

@[expose] def m12B1Tbl : Table :=
  #[7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10, 17, 20, 13, 12, 19, 15, 22, 21, 14, 16, 23, 18]

@[expose] def m12SigmaTbl : Table :=
  #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

@[expose] def m12IrrRGens : List Table := [m12A1Tbl, m12B1Tbl, m12SigmaTbl]

@[expose] def m12IrrSylowWords : List (List Nat) :=
  [[3, 2, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3, 2],
    [2, 2, 3, 2, 2, 3, 2, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2,
      2, 3],
    [2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 2, 1, 2, 2,
      1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1]]

@[expose] def m12IrrSylowTbls : List Table := m12IrrSylowWords.map (wordTbl 24 m12IrrRGens)

@[expose] def m12IrrSift (T : Table) : Bool := decide (ap T 0 < 12)

@[expose] def m12IrrOK : Bool :=
  m12IrrRGens.all (permOK 24) && irrSylowOK 24 200 128 m12IrrSylowTbls m12IrrSift []

end CFSG.Sporadic.SmallOddCore
