
module

public import Certificates.Certificate10077Base
import all Certificates.Certificate10077Base

public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
import Certificates.Kernel.Co1M.Frame10077
import Certificates.Kernel.Co1M.TreeX10077
import Certificates.Kernel.Co1M.TreeY10077
import Certificates.Kernel.Co1M.S10077
import Certificates.Kernel.Co1M.Cent10077
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KD.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.TreeK

end CertificateChecks.KernelCo1M

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1.Module.TwoB in
theorem certificate10077 :
    (∃ W : TwoBW, TwoBOK W)
    ∧ (centB = true) :=
  ⟨⟨KernelCo1M.w77, KernelCo1M.ok77⟩, KernelCo1M.c77_centB⟩

end Certificates
