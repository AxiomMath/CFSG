module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagCert
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2FlagData
import Certificates.Kernel.UnitarySix.FlagW
public import Mathlib
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

namespace CertificateChecks.Batch3701

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

set_option maxRecDepth 100000

private theorem y0Check2_eq_true_0 : y0Check2 = true := by
  decide +kernel

private theorem aIndepCheck_eq_true_2 : aIndepCheck = true := by
  decide +kernel

private theorem aConjCheck2_eq_true_3 : aConjCheck2 = true := by
  decide +kernel

private theorem shapeCheck_eq_true_5 : shapeCheck = true := by
  decide +kernel

private theorem witCheck_eq_true_6 : witCheck = true := by
  decide +kernel

private theorem tnCheck_eq_true_7 : tnCheck = true := by
  decide +kernel

end CertificateChecks.Batch3701

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaN2 in
theorem certificate3701 : (y0Check2 = true) ∧ (dCheck2W = true) ∧ (aIndepCheck = true) ∧ (aConjCheck2 = true) ∧
    (s2CheckW = true) ∧ (shapeCheck = true) ∧ (witCheck = true) ∧ (tnCheck = true) := by
  exact ⟨CertificateChecks.Batch3701.y0Check2_eq_true_0, KernelU6.dCheck2W_true, CertificateChecks.Batch3701.aIndepCheck_eq_true_2,
    CertificateChecks.Batch3701.aConjCheck2_eq_true_3, KernelU6.s2CheckW_true, CertificateChecks.Batch3701.shapeCheck_eq_true_5,
    CertificateChecks.Batch3701.witCheck_eq_true_6, CertificateChecks.Batch3701.tnCheck_eq_true_7⟩

end Certificates
