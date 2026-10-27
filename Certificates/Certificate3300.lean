module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvData
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSurvData
public import Mathlib
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace CertificateChecks.Batch3300

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

set_option maxRecDepth 100000

private theorem lCheck_eq_true_0 : lCheck = true := by
  decide +kernel

private theorem uCheck_eq_true_1 : uCheck = true := by
  decide +kernel

private theorem cCheck_eq_true_2 : cCheck = true := by
  decide +kernel

private theorem tCheck_eq_true_3 : tCheck = true := by
  decide +kernel

end CertificateChecks.Batch3300

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3300 : (lCheck = true) ∧ (uCheck = true) ∧ (cCheck = true) ∧ (tCheck = true) := by
  exact ⟨CertificateChecks.Batch3300.lCheck_eq_true_0, CertificateChecks.Batch3300.uCheck_eq_true_1, CertificateChecks.Batch3300.cCheck_eq_true_2,
    CertificateChecks.Batch3300.tCheck_eq_true_3⟩

end Certificates
