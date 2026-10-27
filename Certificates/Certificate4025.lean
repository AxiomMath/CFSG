module

public import CFSG.Sporadic.J4.QTRankInvNative
import Certificates.Kernel.J4Q.C4025

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem certificate4025 : (invAllOK = true)
    ∧ (∀ e < 1024, isInvE e = true → ∃ x ∈ invData, x.1 = e)
    ∧ (∀ o ∈ orbits, o.1 = 1 ∨ o.1 = 3) := KernelJ4Q.c4025

end Certificates
