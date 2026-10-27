module

public import Certificates.Data.SmithL6Aut
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithL6K.GlueT

public section

namespace Certificates

open CertificateChecks

theorem certificate38606 : CFSG.SmithL6.K.Reach 1953 1953 (· == 0) (fun g u v => CFSG.SmithL6.tvImg g u == v) ∧
    CFSG.SmithL6.chkPtFix = true :=
  ⟨KernelSmithL6K.reach_conv, KernelSmithL6K.ptFix_holds⟩

end Certificates
