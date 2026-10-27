module

public import Certificates.Data.SmithL6Stab
public import Certificates.Data.Kernel.SmithL6K
import Certificates.Kernel.SmithL6K.GlueT

public section

namespace Certificates

open CertificateChecks

theorem certificate38650 : CFSG.SmithL6.K.Reach 1953 1953 (fun a => a == CFSG.SmithL6.stabRep (CFSG.SmithL6.stabCls a))
      (fun g u v => CFSG.SmithL6.tvImg g 0 == 0 && CFSG.SmithL6.tvImg g u == v &&
        CFSG.SmithL6.stabCls u == CFSG.SmithL6.stabCls v) ∧
    CFSG.SmithL6.K.Reach 1953 1953 (· == 0) (fun g u v => CFSG.SmithL6.tvImg g u == v) ∧
    CFSG.SmithL6.chkStabCard = true ∧ CFSG.SmithL6.chkStabComm = true :=
  ⟨KernelSmithL6K.reach_stab, KernelSmithL6K.reach_conv, KernelSmithL6K.stabCard_holds,
    KernelSmithL6K.stabComm_holds⟩

end Certificates
