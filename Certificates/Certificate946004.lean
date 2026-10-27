module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertSpec
import CFSG.Certificates.Kernel.GGToral.PkSound
import Certificates.Kernel.GGToral.Checks
import Certificates.Kernel.GGToral.Head
import Certificates.Kernel.GGToral.Tag

public section


open CFSG.StandardType.StepTwoToralCert CFSG.Blueprint.Chevalley

public section

open CFSG.KC.GGToral CertificateChecks.KernelGGToral CFSG.Blueprint.Chevalley

namespace Certificates

open CFSG.StandardType.StepTwoToralCert CFSG.Blueprint.Chevalley in
theorem certificate946004 : SplitCertSpec .E8 7 ⊤ :=
  pkSplit_sound (τ := .E8) (by norm_num) ch946004_E87 ch946004_hd_E87 ch946004_tag_E87

end Certificates
