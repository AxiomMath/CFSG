module

public import Certificates.Data.Kernel.Co1B
public import Certificates.Kernel.Co1M.D16956
public import Certificates.Kernel.VecCert.Co1.Data
public import Certificates.Kernel.Co1Cover.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1M

open CFSG.KD.C16956 CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1M CFSG.KC.VecK
  CertificateChecks.KernelVec.Co1 CertificateChecks.KernelCo1Cover

theorem c16956_base : (eqK (getL 0 M16956 0) R0 && eqK (getL 0 M16956 1) R1) = true := by
  quickRfl

theorem c16956_mem : (orbMemK 98280 (lk S 32) 17 U1_16956 &&
    orbMemK 98280 (lk S 32) 17 U2_16956) = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
