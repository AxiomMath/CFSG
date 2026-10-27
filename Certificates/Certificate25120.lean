module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.SquaresNative
import Certificates.Kernel.J4F2.J4Std

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std in
theorem certificate25120 : chkSq (locMats ()) (locInvs ()) = true := KernelJ4F2.c25120

end Certificates
