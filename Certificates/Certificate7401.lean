module

public import CFSG.Quasithin.Background.F7TwoInvSporJ4Inputs
import Certificates.Kernel.J4F2.Comm
public import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.F7Two in
theorem certificate7401 : (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaA ()) 5) idRows = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaA ()) 1) idRows = false)
    ∧ (wfRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaA ()) 1) = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaB ()) 30) idRows = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaB ()) 2) idRows = false)
    ∧ (wfRows (CFSG.Sporadic.J4.Native.powRows (j4CommEtaB ()) 2) = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommAB ()) 10) idRows = true)
    ∧ (eqRows (CFSG.Sporadic.J4.Native.powRows (j4CommAB ()) 2) idRows = false)
    ∧ (wfRows (CFSG.Sporadic.J4.Native.powRows (j4CommAB ()) 2) = true)
    ∧ (wfRows idRows = true) := KernelJ4F2.c7401

end Certificates
