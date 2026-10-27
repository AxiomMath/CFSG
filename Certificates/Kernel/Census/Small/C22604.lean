module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22604 :
    (∀ e f : SE, SE.O4E e → ¬ SE.predF e → SE.O4F f → ¬ SE.predE f → ¬ SE.commZ e f) ∧
    (∀ e f : SE, SE.predE e → SE.predE f → SE.commZ e f) ∧
    (∀ e f : SE, SE.predF e → SE.predF f → SE.commZ e f) ∧
    (∀ e : SE, SE.predE e → SE.O4E e ∨ ∃ u v : SE, SE.O4E u ∧ SE.O4E v ∧ e = u * v) ∧
    (∀ e : SE, SE.predF e → SE.O4F e ∨ ∃ u v : SE, SE.O4F u ∧ SE.O4F v ∧ e = u * v) := by
  repeat' apply And.intro
  all_goals decide +kernel

end CertificateChecks.KernelCensus
