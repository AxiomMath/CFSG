module

public import Certificates.Data.SmithL6Check
import Certificates.Kernel.SmithL6K.GluePr

public section

namespace Certificates

theorem certificate38601 :
    CFSG.SmithL6.chkTvInv = true ∧ CFSG.SmithL6.chkPairs = true ∧ CFSG.SmithL6.chkTW = true ∧
      CFSG.SmithL6.chkFormInv = true :=
  ⟨CFSG.SmithL6.K.chkTvInv_holds, CertificateChecks.KernelSmithL6K.pairs_holds,
    CertificateChecks.KernelSmithL6K.tw_holds, CertificateChecks.KernelSmithL6K.formInv_holds⟩

end Certificates
