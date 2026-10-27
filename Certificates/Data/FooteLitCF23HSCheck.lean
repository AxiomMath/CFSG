module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I.HS

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def gens12 : List Table :=
  [hsCentTbl 6, hsCentTbl 7, hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16]

@[expose] def gens4 : List Table := [hsCentTbl 35, hsCentTbl 36, hsCentTbl 37, hsCentTbl 38]

@[expose] def d0Tbl : Table :=
  compT 3850 (compT 3850 (compT 3850 (hsCentTbl 13) (hsCentTbl 13)) (hsCentTbl 14)) (hsCentTbl 13)

@[expose] def c0Tbl : Table := wordTbl 3850 gens12 [1, 6, 1, 6, 2, 2]

@[expose] def xTbl : Table := wordTbl 3850 gens4 [2]

@[expose] def yTbl : Table := wordTbl 3850 gens4 [1, 3]

@[expose] def hsFusOK : Bool :=
  gens12.all (permOK 3850) && gens4.all (permOK 3850) && permOK 3850 (hsCentTbl 12) &&
    involOK 3850 d0Tbl && invOK 3850 c0Tbl (invT 3850 c0Tbl) &&
    tblEq 3850 (compT 3850 (compT 3850 (invT 3850 c0Tbl) (hsCentTbl 12)) c0Tbl)
      (compT 3850 (hsCentTbl 12) d0Tbl) &&
    ordTest 3850 3 xTbl && ordTest 3850 5 yTbl && ordTest 3850 6 (compT 3850 xTbl yTbl)

end CFSG.ComponentClassification.GSThmB.CF23I.HS
