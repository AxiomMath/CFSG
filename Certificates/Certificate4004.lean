module

public import CFSG.Sporadic.J4.QT2LocFiveNative
import Certificates.Kernel.J4Q.C4004

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem certificate4004 : (chkFivePow = true)
    ∧ (chkFiveMasks = true) := KernelJ4Q.c4004

end Certificates
