module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsCert
import Certificates.Kernel.UnitarySix.FormsW

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3193 : (formsCheckW = true) := by
  exact KernelU6.formsCheckW_true

end Certificates
