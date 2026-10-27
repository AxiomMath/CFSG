module

public import Certificates.Kernel.MonsterB.CodeAdj

public section

open CFSG.Monster.B.GSide CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3178

open CFSG.Monster.B.GSide CertificateChecks.KernelMonB

set_option maxRecDepth 100000

theorem kAdj : codeAdjK 6144 6175 = true ∧ codeAdjK 6175 24606 = true ∧
    codeAdjK 24606 6144 = true ∧ codeAdjK 6175 2652785 = true ∧ codeAdjK 2652785 6144 = true ∧
    codeAdjK 24606 2652785 = false := by
  decide +kernel

end CertificateChecks.Batch3178

namespace Certificates

open CertificateChecks.Batch3178 in
open CFSG.Monster.B.GSide in
theorem certificate3178 : (codeGraph.Adj 6144 6175)
    ∧ (codeGraph.Adj 6175 24606)
    ∧ (codeGraph.Adj 24606 6144)
    ∧ (codeGraph.Adj 6175 2652785)
    ∧ (codeGraph.Adj 2652785 6144)
    ∧ (¬ codeGraph.Adj 24606 2652785) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kAdj
  have e : ∀ a b, codeGraph.Adj a b ↔ codeAdjK a b = true := fun a b => by
    rw [← codeAdj_eq]
    rfl
  refine ⟨(e _ _).2 h1, (e _ _).2 h2, (e _ _).2 h3, (e _ _).2 h4, (e _ _).2 h5, ?_⟩
  rw [e, h6]
  exact Bool.false_ne_true

end Certificates
