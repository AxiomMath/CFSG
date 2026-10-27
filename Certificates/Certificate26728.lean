module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Certificate26724
import Certificates.Kernel.HNFFib.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26728 : 739200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[8]!)).ncard :=
  calc 739200 = 35200 * 21 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_right 21 Certificates.certificate26724
    _ ≤ _ := KernelHNFFib.bound8

end Certificates
