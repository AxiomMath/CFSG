module

public import CFSG.Sporadic.J4.QTOutObsNative
import Certificates.Kernel.J4Q.C4023
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem certificate4023 : (wfRows e5Rows = true ∧ wfRows gRows = true ∧ wfRows yRows = true)
    ∧ (eqRows (mulRows yRows yRows) idRows = true)
    ∧ (eqRows (mulRows (mulRows yRows e5Rows) yRows) (mulRows (etaR cB) hRows) = true)
    ∧ (∀ ℓ ∈ wObs, ℓ ∈ CFSG.Sporadic.J4.QT.letters)
    ∧ (∀ f ∈ fvs, (frApply (frTable e5Rows) f).beq f = true)
    ∧ (triOK fvs fps = true)
    ∧ (triOK ximgs xps = true)
    ∧ (fvs.size = 62 ∧ xvs.size = 51)
    ∧ (cA < 2 ^ 11 ∧ cB < 2 ^ 11) := KernelJ4Q.c4023

end Certificates
