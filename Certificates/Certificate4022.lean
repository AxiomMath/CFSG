module

public import CFSG.Sporadic.J4.QTOutMatNative
import Certificates.Kernel.J4Q.C4022
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem certificate4022 : (eqRows (CFSG.Sporadic.J4.Native.powRows (xRowsOf 1) 23) idRows = true)
    ∧ (wfRows (xRowsOf 1) = true)
    ∧ (eqRows (xRowsOf 1) idRows = false) := KernelJ4Q.c4022

end Certificates
