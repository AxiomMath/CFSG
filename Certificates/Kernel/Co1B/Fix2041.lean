module

public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1B.Data2041
public import Certificates.Data.Kernel.Co1BFix
public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CertificateChecks.KernelCo1Cover

theorem trA_chk : Nat.beq (trK 24 (getL oneK IRS 23)) TA = true := by quickRfl
theorem trC_chk : Nat.beq (trK 24 (getL oneK IRS 51)) TC = true := by quickRfl
theorem tr1_chk : Nat.beq (trK 24 R0) T1 = true := by quickRfl

theorem fixA_chk : Nat.beq (fixTabK TA CV.F 117) 2280 = true := by quickRfl
theorem fixC_chk : Nat.beq (fixTabK TC CV.F 117) 264 = true := by quickRfl
theorem fix1_chk : Nat.beq (fixTabK T1 CV.F 117) 0 = true := by quickRfl

theorem sq_chk : CFSG.KLie.CT.andB (Nat.beq (mulWK (getL oneK IRS 23) (getL oneK IRS 23)) oneK)
    (CFSG.KLie.CT.andB (Nat.beq (mulWK (getL oneK IRS 51) (getL oneK IRS 51)) oneK)
      (Nat.beq (mulWK R0 R0) oneK)) = true := by quickRfl

theorem ne_chk : CFSG.KLie.CT.andB (unpackR 24 (getL oneK IRS 23) != unpackR 24 oneK)
    (CFSG.KLie.CT.andB (unpackR 24 (getL oneK IRS 51) != unpackR 24 oneK)
      (unpackR 24 R0 != unpackR 24 oneK)) = true := by quickRfl

end CertificateChecks.KernelCo1B

end
