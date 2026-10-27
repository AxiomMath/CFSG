module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNFOrb.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26722 : 2200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[2]!)).ncard := KernelHNFOrb.bound2

end Certificates
