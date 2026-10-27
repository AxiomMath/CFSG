module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2PermData
import Certificates.Kernel.J4M2.C4202Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M2 in
theorem certificate4202 : chkSig = true ∧ chkHex = true ∧ chkWords = true ∧ chkT = true ∧ chkClass = true := KernelJ4M2.chk4202

end Certificates
