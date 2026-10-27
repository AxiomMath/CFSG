module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNFOrb.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26723 : 5775 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[3]!)).ncard := KernelHNFOrb.bound3

end Certificates
