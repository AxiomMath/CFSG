module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Certificate26723
import Certificates.Kernel.HNFFib.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26726 : 277200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[6]!)).ncard :=
  calc 277200 = 5775 * 48 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_right 48 Certificates.certificate26723
    _ ≤ _ := KernelHNFFib.bound6

end Certificates
