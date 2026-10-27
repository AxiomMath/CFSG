module

public import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.J2DataInputs

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I.J2

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def d0Tbl : Table := wordTbl 315 j2DGens [1, 2, 2]

@[expose] def c0Tbl : Table := wordTbl 315 (j2C1Gens ++ j2C2Gens) [9, 5, 6, 9]

@[expose] def j2FusOK : Bool :=
  (j2C1Gens ++ j2C2Gens).all (permOK 315) && j2DGens.all (permOK 315) &&
    permOK 315 (j2CentTbl 17) && involOK 315 d0Tbl && invOK 315 c0Tbl (invT 315 c0Tbl) &&
    tblEq 315 (compT 315 (compT 315 (invT 315 c0Tbl) (j2CentTbl 17)) c0Tbl)
      (compT 315 (j2CentTbl 17) d0Tbl)

end CFSG.ComponentClassification.GSThmB.CF23I.J2
