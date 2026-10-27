module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Certificate26722
import Certificates.Kernel.HNFFib.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26725 : 123200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[5]!)).ncard :=
  calc 123200 = 2200 * 56 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_right 56 Certificates.certificate26722
    _ ≤ _ := KernelHNFFib.bound5

end Certificates
