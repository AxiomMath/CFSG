module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2IdData
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2IdData
public import Mathlib
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

namespace CertificateChecks.Batch3702

open CFSG.EvenSmallLie.UnitarySix.YamadaN2

private theorem commDecCheck_eq_true_0 : commDecCheck = true := by
  decide +kernel

private theorem uIdCheck_eq_true_1 : uIdCheck = true := by
  decide +kernel

private theorem lIdCheck_eq_true_2 : lIdCheck = true := by
  decide +kernel

private theorem tlCheck_eq_true_3 : tlCheck = true := by
  decide +kernel

end CertificateChecks.Batch3702

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaN2 in
theorem certificate3702 : (commDecCheck = true) ∧ (uIdCheck = true) ∧ (lIdCheck = true) ∧ (tlCheck = true) := by
  exact ⟨CertificateChecks.Batch3702.commDecCheck_eq_true_0, CertificateChecks.Batch3702.uIdCheck_eq_true_1,
    CertificateChecks.Batch3702.lIdCheck_eq_true_2, CertificateChecks.Batch3702.tlCheck_eq_true_3⟩

end Certificates
