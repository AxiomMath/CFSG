module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Cert
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Data
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Data
import Certificates.Kernel.UnitarySix.N2W
public import Mathlib
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

namespace CertificateChecks.Batch3700

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

set_option maxRecDepth 100000

private theorem kGenCheck_eq_true_0 : kGenCheck = true := by
  decide +kernel

private theorem commValid_eq_true_1 : commValid = true := by
  decide +kernel

end CertificateChecks.Batch3700

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaN2 in
theorem certificate3700 : (kGenCheck = true) ∧ (commValid = true) ∧ (h1Check9W = true) := by
  exact ⟨CertificateChecks.Batch3700.kGenCheck_eq_true_0, CertificateChecks.Batch3700.commValid_eq_true_1, KernelU6.h1Check9W_true⟩

end Certificates
