module

public import Certificates.Data.Kernel.ASVolI.K43K7278
public import Certificates.Kernel.HMathieu.T24
import all Init.Data.Array.Basic
import all Init.Data.List.Basic

public section

namespace CertificateChecks.KernelASVolI

open CFSG.KS.ASVolI CertificateChecks.KernelHMathieu

theorem k43_sylK : sylK T24.E = true := by
  decide +kernel

theorem k43_classK : classK T24.E = true := by
  decide +kernel

theorem k43_modK : modK T24.E = true := by
  decide +kernel

end CertificateChecks.KernelASVolI

end
