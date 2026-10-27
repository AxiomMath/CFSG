module

public import CFSG.Sporadic.J4.QT2ANative
import Certificates.Kernel.J4Q.C4000

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2A in
theorem certificate4000 : (chkMod = true)
    ∧ (chkY = true)
    ∧ (chkYr (y5R ()) 5 = true)
    ∧ (chkYr (y7R ()) 7 = true)
    ∧ (chkYr (y11R ()) 11 = true)
    ∧ (chkQgens = true)
    ∧ (chkNotQzY = true)
    ∧ (chkNotQzPow (y5R ()) 5 = true)
    ∧ (chkNotQzPow (y7R ()) 7 = true)
    ∧ (chkNotQzPow (y11R ()) 11 = true)
    ∧ (chkWit = true)
    ∧ (chkE = true)
    ∧ (chkQconj = true)
    ∧ (chkLoc = true) := KernelJ4Q.c4000

end Certificates
