module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Kernel.Co2Cent.CentData
public import Certificates.Kernel.Co2Cent.CentBData
public import Certificates.Data.Kernel.OrbRow.CentB
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp

theorem ch17351_bx : bAnd(fixSetK 2300 12 4095 xB FB, bAnd(Nat.beq (lenS FB) 41,
    bAnd(allN 41 (fun t => Nat.blt (getS FB t) 2300), incK FB 0 0))) = true := by
  quickRfl

theorem ch17351_bd : allN 41 (fun t => strictB (getS FB t) fun p =>
    degK 2300 12 4095 SB 17 (getS MB 0) (getS BB 0) (getS DB 1) FB p
      (nIf(Nat.beq p 1, 40, 13)) (getLs UW t)) = true := by
  quickRfl

theorem ch17351_bc : bAnd(capK (getS DB 2) FB 27, bAnd(capK (getS DB 3) FB 6,
    bAnd(capK (getS DB 4) FB 4, capK (getS DB 5) FB 2))) = true := by
  quickRfl

theorem ch17351_bv :
    regK 2300 12 4095 SB 17 (getS MB 6) (getS BB 6) (getS DB 6) VQ VW 6 xB 3 = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
