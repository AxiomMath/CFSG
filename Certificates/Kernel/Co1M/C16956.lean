module

public import Certificates.Data.Kernel.Co1M.ThirteenScan
public import Certificates.Kernel.Co1M.D16956
public import Certificates.Kernel.VecCert.Co1.Data
public import CFSG.Certificates.Kernel.Co1M.OrbitMem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1Thirteen CFSG.KD.C16956 CFSG.KC.Co1M CFSG.KC.VecK CFSG.KC.Co1F2
  CertificateChecks.KernelVec.Co1

theorem c16956_ok : thirteenOK (orbMemK 98280 (lk S 32) 17) (getL 0 M16956) (getL 0 MI16956) 247
    WS16956 IX16956 TK16956 TS16956 Q16956 U1_16956 U2_16956 UM16956 CT16956 = true := by
  quickRfl

end CertificateChecks.KernelCo1M

end
