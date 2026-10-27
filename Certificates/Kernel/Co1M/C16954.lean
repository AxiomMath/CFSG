module

public import Certificates.Data.Kernel.Co1M.ElevenFix
public import Certificates.Kernel.Co1M.D16954
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1ElevenFix CFSG.KD.C16954 CFSG.KC.Co1M CFSG.KC.VecK
  CertificateChecks.KernelVec.Co1 CertificateChecks.KernelCo1Cover

theorem c16954_ok : elevenFixOK (orbMemK 98280 (lk S 32) 17) [R0, R1] DV16954 RS16954 RIS16954
    W16954 NF16954 U16954 52 53 11 3 20 10 = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
