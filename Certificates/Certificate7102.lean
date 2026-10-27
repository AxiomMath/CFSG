module

public import CFSG.Quasithin.H13.L32NKGCertInputs
import Certificates.Kernel.Misc.G22W.Final

public section

namespace Certificates

theorem certificate7102 : CFSG.Quasithin.H13.KGCert.g22Elems.length = 12096 ∧
    CFSG.Quasithin.H13.KGCert.oneC ∈ CFSG.Quasithin.H13.KGCert.g22Elems ∧
    CFSG.Quasithin.H13.KGCert.g22ValidCheck = true ∧
    CFSG.Quasithin.H13.KGCert.g22ClosedCheck = true ∧
    CFSG.Quasithin.H13.KGCert.g22StabCheck = true ∧
    CFSG.Quasithin.H13.KGCert.g22NodupCheck = true :=
  CFSG.KD.G22W.cert7102_ok

end Certificates
