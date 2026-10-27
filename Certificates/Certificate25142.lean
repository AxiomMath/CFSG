module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataModLiftNative
import Certificates.Kernel.J4F2.J4Std

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native CFSG.EvenSporadicStandard.J4Std.DataMod in
theorem certificate25142 : chkLift (locMats ()) (locInvs ()) = true := KernelJ4F2.c25142

end Certificates
