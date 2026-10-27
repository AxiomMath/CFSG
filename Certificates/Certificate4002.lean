module

public import CFSG.Sporadic.J4.QT2LocNative
import Certificates.Kernel.J4Q.C4002

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem certificate4002 : (chkTClosed = true)
    ∧ (chkD (locMats ()) (locInvs ()) = true)
    ∧ ((1 : Nat) ∈ tMasks) := KernelJ4Q.c4002

end Certificates
