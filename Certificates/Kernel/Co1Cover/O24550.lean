module

public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.Co1Cover.EData
public import Certificates.Data.Kernel.VOrbRec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1Cover.ECore

open CFSG.KC.VOrbRec CFSG.KLie.CT CertificateChecks.KernelCo1Cover

theorem orbC_ok : vorbRecK 11 TAP TBP 1 1288 KC RC = true := by quickRfl

theorem orbA_ok : vorbRecK 11 TAP TBP 3 759 KA RA = true := by quickRfl

theorem xC_notA : notB (bit KA 1) = true := by quickRfl

theorem cover_ok : allN 2048 (fun w => orB (Nat.beq w 0) (orB (bit KC w) (bit KA w))) = true := by
  quickRfl

end CertificateChecks.KernelCo1Cover.ECore

end
