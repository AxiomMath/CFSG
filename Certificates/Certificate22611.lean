module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisPauliCertInputs
import Certificates.Kernel.Census.Small.C22611
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.SCert CFSG.Quasithin.HSType in
theorem certificate22611 :
    (∀ p q : Pauli2, SE.pauliE (p * q) = SE.pauliE p * SE.pauliE q) ∧
    (∀ p : Pauli2, SE.predE (SE.pauliE p)) ∧
    (∀ p : Pauli2, SE.pauliE p = 1 → p = 1) ∧
    (∀ k : SE, 4 ≤ k.d.val → ¬ SE.predE (k⁻¹ * (SE.gen 6)⁻¹ * k * SE.gen 6) ∨
      ¬ SE.predE (k⁻¹ * (SE.gen 7)⁻¹ * k * SE.gen 7)) := KernelCensus.check22611

end Certificates
