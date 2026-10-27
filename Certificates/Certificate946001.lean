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
theorem certificate946001 : SplitCertSpec .F4 3 ⊤ ∧ SplitCertSpec .E6 3 ⊤ ∧ SplitCertSpec .E6 5 ⊤ ∧
    SplitCertSpec .E7 3 ⊤ ∧ SplitCertSpec .E7 5 ⊤ ∧ SplitCertSpec .E7 7 ⊤ ∧
    SplitCertSpec .E8 3 ⊤ ∧ SplitCertSpec .E8 5 ⊤ :=
  ⟨pkSplit_sound (τ := .F4) (by norm_num) ch946001_F43 ch946001_hd_F43 ch946001_tag_F43,
    pkSplit_sound (τ := .E6) (by norm_num) ch946001_E63 ch946001_hd_E63 ch946001_tag_E63,
    pkSplit_sound (τ := .E6) (by norm_num) ch946001_E65 ch946001_hd_E65 ch946001_tag_E65,
    pkSplit_sound (τ := .E7) (by norm_num) ch946001_E73 ch946001_hd_E73 ch946001_tag_E73,
    pkSplit_sound (τ := .E7) (by norm_num) ch946001_E75 ch946001_hd_E75 ch946001_tag_E75,
    pkSplit_sound (τ := .E7) (by norm_num) ch946001_E77 ch946001_hd_E77 ch946001_tag_E77,
    pkSplit_sound (τ := .E8) (by norm_num) ch946001_E83 ch946001_hd_E83 ch946001_tag_E83,
    pkSplit_sound (τ := .E8) (by norm_num) ch946001_E85 ch946001_hd_E85 ch946001_tag_E85⟩

end Certificates
