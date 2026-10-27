module

public import Certificates.Kernel.Co1Three.Data
public import Certificates.Kernel.Co1ThreeK.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Three

open CFSG.KC.Enum

theorem rootsR :
    allN 3 (fun j => Nat.beq (TS (Nat.add j 8)) (CertificateChecks.KernelCo1ThreeK.R.M j)) = true := by
  quickRfl

end CertificateChecks.KernelCo1Three

end
