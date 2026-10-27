module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelData
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelData
public import Mathlib
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace CertificateChecks.Batch3194

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

private theorem wordCheck_eq_true_0 : wordCheck = true := by
  decide +kernel

private theorem embedCheck_eq_true_1 : embedCheck = true := by
  decide +kernel

private theorem aKerCheck_eq_true_2 : aKerCheck = true := by
  decide +kernel

private theorem indepCheck_eq_true_3 : indepCheck = true := by
  decide +kernel

end CertificateChecks.Batch3194

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3194 : (wordCheck = true)
    ∧ (embedCheck = true)
    ∧ (aKerCheck = true)
    ∧ (indepCheck = true) := by
  exact ⟨CertificateChecks.Batch3194.wordCheck_eq_true_0, CertificateChecks.Batch3194.embedCheck_eq_true_1,
    CertificateChecks.Batch3194.aKerCheck_eq_true_2, CertificateChecks.Batch3194.indepCheck_eq_true_3⟩

end Certificates
