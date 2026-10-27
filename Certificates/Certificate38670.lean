module

public import Certificates.Data.SmithL6Pair
import Certificates.Kernel.SmithL6K.GlueOp

public section

namespace Certificates

open CertificateChecks

theorem certificate38670 : CFSG.SmithL6.prChkStd = true ∧ CFSG.SmithL6.prChkOrd4 = true ∧
    CFSG.SmithL6.prChkF3 = true :=
  ⟨KernelSmithL6K.prStd_holds, KernelSmithL6K.prOrd4_holds, KernelSmithL6K.prF3_holds⟩

end Certificates
