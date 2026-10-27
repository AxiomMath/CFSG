
module


public import Certificates.Kernel.Sporadic.Fi24R2W.Group

public section

namespace Certificates

open CertificateChecks

theorem certificate2076 : CFSG.Sporadic.FischerOddCore.FPtsFacts ∧     CFSG.Sporadic.FischerOddCore.R2Facts :=
  ⟨KernelSpor.Fi24R2W.fpts_facts, by intros; exact KernelSpor.Fi24R2W.r2_facts⟩

end Certificates
