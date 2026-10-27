module

public import CFSG.Sporadic.J4.QTRankWitNative
import Certificates.Kernel.J4Q.C4026

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Sporadic.J4.Native in
theorem certificate4026 : (eqRows (CFSG.Sporadic.J4.Native.powRows (X11 ()) 11) idRows = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (Y11 ()) 11) idRows = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (Z11 ()) 11) idRows = true)
    ∧ (eqRows (Z11 ()) idRows = false)
    ∧ (wfRows (Z11 ()) = true ∧ wfRows idRows = true)
    ∧ (eqRows (mulRows (X11 ()) (Z11 ())) (mulRows (Z11 ()) (X11 ())) = true)
    ∧ (eqRows (mulRows (Y11 ()) (Z11 ())) (mulRows (Z11 ()) (Y11 ())) = true)
    ∧ (eqRows (mulRows (mulRows rowsA (X11 ())) rowsA) (CFSG.Sporadic.J4.Native.powRows (X11 ()) 10) = true)
    ∧ (eqRows (mulRows rowsA (Z11 ())) (mulRows (Z11 ()) rowsA) = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (C37 ()) 37) idRows = true)
    ∧ (eqRows (C37 ()) idRows = false)
    ∧ (wfRows (C37 ()) = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (AE5 ()) 11) idRows = true)
    ∧ (∃ o ∈ orbits, o.1 = 3 ∧ ∃ p ∈ o.2.1, p.1 = 5) := KernelJ4Q.c4026

end Certificates
