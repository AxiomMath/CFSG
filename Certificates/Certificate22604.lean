module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
import Certificates.Kernel.Census.Small.C22604

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert in
theorem certificate22604 :
    (∀ e f : SE, SE.O4E e → ¬ SE.predF e → SE.O4F f → ¬ SE.predE f → ¬ SE.commZ e f) ∧
    (∀ e f : SE, SE.predE e → SE.predE f → SE.commZ e f) ∧
    (∀ e f : SE, SE.predF e → SE.predF f → SE.commZ e f) ∧
    (∀ e : SE, SE.predE e → SE.O4E e ∨ ∃ u v : SE, SE.O4E u ∧ SE.O4E v ∧ e = u * v) ∧
    (∀ e : SE, SE.predF e → SE.O4F e ∨ ∃ u v : SE, SE.O4F u ∧ SE.O4F v ∧ e = u * v) := KernelCensus.check22604

end Certificates
