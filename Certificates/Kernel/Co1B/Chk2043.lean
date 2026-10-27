
module

public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1B.Data2041
public import Certificates.Kernel.Co1B.Data2043
public import Certificates.Kernel.Co1Cover.Checks
public import Certificates.Data.Kernel.Co1BAct
public import Certificates.Data.Kernel.Co1B
public import CFSG.Sporadic.Co1Block.PermData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CertificateChecks.KernelCo1Cover

theorem trA_chk' : Nat.beq (trK 24 R0) T1 = true := by quickRfl

theorem trB_chk : Nat.beq (trK 24 R1) TB = true := by quickRfl

theorem basis_chk : recAllB (fun t => Nat.beq (CFSG.KC.M1F2.rowF 24 BR t)
    (CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) (CV.F 0) (getL 0 CFSG.Sporadic.Co1Block.certBasisIdx t)))
    24 = true := by quickRfl

theorem basisInv_chk : CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (canK BR) (canK BI))
    (Nat.beq (mulK BR BI) oneK) = true := by quickRfl

theorem basisLeft_chk : Nat.beq (mulK BI BR) oneK = true := by quickRfl

theorem v0_chk : Nat.beq (CFSG.KC.Enum.pg 24 (CFSG.KS.mask 24) (CV.F 0) 0) 16663704 = true := by
  quickRfl

end CertificateChecks.KernelCo1B

end
