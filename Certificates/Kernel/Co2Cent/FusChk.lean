module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Kernel.Co2Cent.CentData
public import Certificates.Kernel.Co2Cent.FusData
public import Certificates.Data.Kernel.OrbRow.Fus
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp CFSG.KS

theorem ch17351_fh : allN 40 (fun j => wordEqK 2300 12 SB 17 (getS MB 0) (getS H j) (getLs HW j)) =
    true := by
  quickRfl

theorem ch17351_fk : bAnd(allN 80 (fun t => fusK 2300 12 (mask 12) DG H xA xB FI FC FE (Nat.succ t)),
    bAnd(Nat.beq (getS FC 5) 0, Nat.beq (getS FC 4) 1)) = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
