module

public import Certificates.Data.CFSGNative.KGroups.Sp6G22
public import CFSG.Quasithin.H13.L32NKGCertInputs
import Certificates.Kernel.Misc.Sp6W.Final

public section

namespace Certificates

open CFSG.KGroups.Sp6 in
theorem certificate4157 : countCheck 64 1451520 = true ∧ normCheck 64 s0 n0List = true ∧
    witCheck 64 CFSG.Quasithin.H13.KGCert.g22Elems n0List 6047 = true :=
  ⟨CFSG.KC.Sp6N.cert4157_count_norm.1, CFSG.KC.Sp6N.cert4157_count_norm.2,
    CFSG.KC.Sp6W.cert4157_wit⟩

end Certificates
