module

public import CFSG.Sporadic.J4.QT2LocZNative
import Certificates.Kernel.J4Q.C4016

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem certificate4016 : (chkCommRoot (locMats ()) (locInvs ()) gWord = true)
    ∧ (chkOrder (locMats ()) (locInvs ()) y7Word 7 = true)
    ∧ (chkOrder (locMats ()) (locInvs ()) y11Word 11 = true) := KernelJ4Q.c4016

end Certificates
