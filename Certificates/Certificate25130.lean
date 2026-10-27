module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11Native
import Certificates.Kernel.J4F2.J4Std

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std.Data11 in
theorem certificate25130 : chkPQ (locMats ()) (locInvs ()) = true := KernelJ4F2.c25130

end Certificates
