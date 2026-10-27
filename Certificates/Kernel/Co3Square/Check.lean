module

public import Certificates.Kernel.Sporadic.Co3.Single
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Square

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor

theorem canon_t0 : canonK 276 9 (mask 9) (276 * 9) (Co3Text.L (Nat.add 35 0)) = true := by
  quickRfl

theorem canon_z : canonK 276 9 (mask 9) (276 * 9) Co3Z = true := by quickRfl

theorem canon_sq : canonK 276 9 (mask 9) (276 * 9)
    (pcomp 276 9 (mask 9) (Co3Text.L (Nat.add 35 0)) (Co3Text.L (Nat.add 35 0))) = true := by
  quickRfl

theorem sq_t0 :
    Nat.beq (pcomp 276 9 (mask 9) (Co3Text.L (Nat.add 35 0)) (Co3Text.L (Nat.add 35 0))) Co3Z =
      true := by
  quickRfl

end CertificateChecks.KernelCo3Square

end
