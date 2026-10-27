module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Cert
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data
import Certificates.Kernel.UnitarySix.H1W
public import Mathlib
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParFormsData
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace CertificateChecks.Batch3191

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

set_option maxRecDepth 100000

private theorem relCheck_eq_true_0 : relCheck = true := by
  decide +kernel

end CertificateChecks.Batch3191

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3191 : (relCheck = true)
    ∧ (h1CheckW = true) := by
  exact ⟨CertificateChecks.Batch3191.relCheck_eq_true_0, KernelU6.h1CheckW_true⟩

end Certificates
