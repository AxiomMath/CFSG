module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisPauliCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG.ComponentClassification.GHarris.SCert CFSG.Quasithin.HSType

theorem pauliE_eq_one_coords : ∀ p : Pauli2, SE.pauliE p = 1 →
    p.a = 0 ∧ p.b = 0 ∧ p.c = 0 ∧ p.d = 0 ∧ p.e = 0 := by
  decide +kernel

open CFSG.ComponentClassification.GHarris.SCert CFSG.Quasithin.HSType in
theorem check22611 :
    (∀ p q : Pauli2, SE.pauliE (p * q) = SE.pauliE p * SE.pauliE q) ∧
    (∀ p : Pauli2, SE.predE (SE.pauliE p)) ∧
    (∀ p : Pauli2, SE.pauliE p = 1 → p = 1) ∧
    (∀ k : SE, 4 ≤ k.d.val → ¬ SE.predE (k⁻¹ * (SE.gen 6)⁻¹ * k * SE.gen 6) ∨
      ¬ SE.predE (k⁻¹ * (SE.gen 7)⁻¹ * k * SE.gen 7)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_, by decide +kernel⟩
  intro p hp
  obtain ⟨ha, hb, hc, hd, he⟩ := pauliE_eq_one_coords p hp
  exact Pauli2.ext ha hb hc hd he

end CertificateChecks.KernelCensus
