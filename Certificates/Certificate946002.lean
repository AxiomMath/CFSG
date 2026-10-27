module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSpec
import CFSG.Certificates.Kernel.GGToral.PkSound
import Certificates.Kernel.GGToral.Checks
import Certificates.Kernel.GGToral.Head
import Certificates.Kernel.GGToral.Tag

public section


open CFSG.StandardType.StepTwoToralCert

public section

open CFSG.KC.GGToral CertificateChecks.KernelGGToral

namespace Certificates

open CFSG.StandardType.StepTwoToralCert in
theorem certificate946002 : TwistCertSpec 3 e6Gamma ∧ TwistCertSpec 5 e6Gamma :=
  ⟨pkTwist_sound (by norm_num) ch946002_TW3 ch946002_hd_TW3 ch946002_tag_TW3,
    pkTwist_sound (by norm_num) ch946002_TW5 ch946002_hd_TW5 ch946002_tag_TW5⟩

end Certificates
