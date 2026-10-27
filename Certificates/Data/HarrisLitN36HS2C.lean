module

public import CFSG.Sporadic.SmallOddCore.HSCheckInputs
public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.ComponentClassification.HarrisLit.N36.HS2C

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native

@[expose] def t2C : Table := hsCentTbl 21

@[expose] def y7 : Table := hsCentTbl 28

@[expose] def g7 : Table := hsCentTbl 24

@[expose] def x7 : Table := compT 3850 (compT 3850 g7 y7) (invT 3850 g7)

@[expose] def y5 : Table := hsCentTbl 26

@[expose] def g5 : Table := compT 3850 (hsCentTbl 25) (hsCentTbl 23)

@[expose] def x5 : Table := compT 3850 (compT 3850 g5 y5) (invT 3850 g5)

@[expose] def big (A : Array Table) (cap N : Nat) : Bool :=
  A.all (permOK 3850) &&
    mulTreeOK 3850 A (mulClosureH 3850 A cap).1 (mulClosureH 3850 A cap).2.1
      (mulClosureH 3850 A cap).2.2 &&
    hkeysDistinct 3850 (mulClosureH 3850 A cap).1.toList &&
    decide (N ≤ (mulClosureH 3850 A cap).1.size)

@[expose] def hs2CCheck : Bool :=
  permOK 3850 t2C && permOK 3850 (hsCentTbl 23) && permOK 3850 (hsCentTbl 25) &&
  permOK 3850 y7 && hsSift y7 && commTT 3850 y7 t2C &&
    tblEq 3850 (powT 3850 7 y7) (idT 3850) &&
  permOK 3850 y5 && hsSift y5 && commTT 3850 y5 t2C &&
    tblEq 3850 (powT 3850 5 y5) (idT 3850) &&
  permOK 3850 g7 && invOK 3850 g7 (invT 3850 g7) &&
  permOK 3850 g5 && invOK 3850 g5 (invT 3850 g5) &&
  big #[y7, x7] 200 169 && big #[y5, x5] 400 361

end CFSG.ComponentClassification.HarrisLit.N36.HS2C
