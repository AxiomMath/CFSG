module

public import CFSG.Sporadic.Co1.Cover.Data
import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.InvDataInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.CoverNative CFSG.Sporadic.Co1.Cover CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative in
theorem certificate10061 :
    (CFSG.Sporadic.Co1.InvNative.validRows (rrCov 4) = true ∧
        CFSG.Sporadic.Co1.InvNative.validRows (rrCov 5) = true)
    ∧ (epsBasicOK epsRows = true)
    ∧ (epsInjOK epsRows = true)
    ∧ (normOK epsRows (rrCov 4) (transposeRows 11 Aa) = true)
    ∧ (normOK epsRows (rrCov 5) (transposeRows 11 Ba) = true)
    ∧ (orderIs t0Rows 2 = true)
    ∧ (CFSG.Sporadic.Co1.Module.countsOK t0Rows 4096 0 = true) := KernelCo1Cover.facts10061

end Certificates
