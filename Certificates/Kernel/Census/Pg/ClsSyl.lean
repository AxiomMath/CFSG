module

public import Certificates.Kernel.Census.Pg.ClsData
public import Certificates.Kernel.Census.Pg.ClsOrb
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPgCls

open CFSG.KC.Enum CFSG.KS CFSG.KC.W16Cls

theorem sylG_ok : allN 4 (fun k => Nat.beq (wordP A (SG k)) (SGP k)) = true := by quickRfl

theorem syl_ok : sylK SGP 4 8192 L LE LP LO = true := by quickRfl

theorem cov_ok : invCovK 8192 L LC Tc NC = true := by quickRfl

end CertificateChecks.KernelPgCls
