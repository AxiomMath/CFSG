module

public import CFSG.Sporadic.J4.QT2LocCntNative
import Certificates.Kernel.J4Q.C4003

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem certificate4003 : (chkZMasks = true)
    ∧ (chkCntZ (locMats ()) (locInvs ()) = true)
    ∧ (vorbOK locTabs rep6Vec orb6 28336 = true)
    ∧ ((List.range 7).all (fun ℓ =>
          eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
            idRows) = true) := KernelJ4Q.c4003

end Certificates
