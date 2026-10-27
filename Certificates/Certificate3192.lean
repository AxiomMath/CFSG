module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDCert
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDData
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParDData
import Certificates.Kernel.UnitarySix.DW
public import Mathlib
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsData
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace CertificateChecks.Batch3192

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

set_option maxRecDepth 100000

private theorem aConjCheck_eq_true_0 : aConjCheck = true := by
  decide +kernel

private theorem y0Check_eq_true_1 : y0Check = true := by
  decide +kernel

end CertificateChecks.Batch3192

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3192 : (aConjCheck = true)
    ∧ (y0Check = true)
    ∧ (dCheckW = true) := by
  exact ⟨CertificateChecks.Batch3192.aConjCheck_eq_true_0, CertificateChecks.Batch3192.y0Check_eq_true_1, KernelU6.dCheckW_true⟩

end Certificates
