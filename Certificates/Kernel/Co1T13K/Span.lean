module

public import Certificates.Data.Kernel.Co1T13KS
public import Certificates.Kernel.Co1T13K.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1T13K

open CFSG.KC.Co1T13K

theorem ch13504span : spanK CFSG.KD.Co1T13K.YT CFSG.KD.Co1T13K.R0 CFSG.KD.Co1T13K.R1
    CFSG.KD.Co1T13K.NT = true := by quickRfl

theorem ch13504move : (!Nat.beq (CFSG.KC.M1F2.vmF 24 (CFSG.KC.Co1F2.getL 0 CFSG.KD.Co1T13K.YT 1) 1) 1)
    = true := by quickRfl

end CertificateChecks.KernelCo1T13K

end
