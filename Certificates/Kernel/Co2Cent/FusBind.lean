module

public import Certificates.Kernel.Co2Cent.CentData
public import Certificates.Kernel.Co2Cent.FusData
public import Certificates.Kernel.Co2Pump.K
public import Certificates.Data.Kernel.OrbRow.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CertificateChecks.KernelMisc.Co2K CertificateChecks.KernelCo2Pump

theorem ch17351_fd : bAnd(allN 4 (fun i => bindK (getS DG i) (DD i) (mmK (DD i) (DD i))),
    bAnd(Nat.beq xA (getS DG 1), Nat.beq xB (getS DG 0))) = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
