module

public import Certificates.Data.J4M2.QStruct
import Certificates.Kernel.J4M2.C4201

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.J4M2 in
theorem certificate4201 : chkQRel = true ∧ chkQC = true ∧ chkQPerf = true := KernelJ4M2.c4201

end Certificates
