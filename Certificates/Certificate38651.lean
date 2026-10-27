module

public import Certificates.Data.SmithL6Facts
import Certificates.Kernel.SmithL6K.GlueA

public section

namespace Certificates

theorem certificate38651 : CFSG.SmithL6.mfChkWt = true ∧ CFSG.SmithL6.mfChkTvAdj = true :=
  ⟨CertificateChecks.KernelSmithL6K.mfChkWt_holds,
    CertificateChecks.KernelSmithL6K.mfChkTvAdj_holds⟩

end Certificates
