module

public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native

@[expose] def hsInvChk (_ : Unit) : Bool :=
  permOK 3850 (hsCentTbl 12) && permOK 3850 (hsCentTbl 21) && permOK 3850 (hsCentTbl 34) &&
    involOK 3850 (hsCentTbl 12) && involOK 3850 (hsCentTbl 21) && involOK 3850 (hsCentTbl 34) &&
    pairTest 3850 6 3 2 2 (hsCentTbl 12) hsPGTbls[0]! &&
    pairTest 3850 8 6 2 5 (hsCentTbl 12) hsPGTbls[1]! &&
    pairTest 3850 6 3 2 2 (hsCentTbl 21) hsPGTbls[0]! &&
    pairTest 3850 8 3 2 5 (hsCentTbl 21) hsPGTbls[1]! &&
    pairTest 3850 6 3 2 2 (hsCentTbl 34) hsPGTbls[0]! &&
    pairTest 3850 30 10 2 5 (hsCentTbl 34) hsPGTbls[1]!

end CFSG.Quasithin.F7Two
