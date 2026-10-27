module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.PlaneFacts
import Certificates.Kernel.Sporadic.ONPl.Facts
import Certificates.Certificate2212

public section

public section

namespace Certificates

open CertificateChecks

open CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair in
theorem certificate753501 : 
    b1P ≠ 1 ∧ qP 2 ≠ 1 ∧ b1P ^ 7 = 1 ∧ qP 2 ^ 7 = 1 ∧ b1P * qP 2 = qP 2 * b1P ∧
    qP 0 * b1P * (qP 0)⁻¹ = b1P ∧ qP 0 * qP 2 * (qP 0)⁻¹ = b1P * qP 2 ∧
    qP 1 * b1P * (qP 1)⁻¹ = b1P * qP 2 ∧ qP 1 * qP 2 * (qP 1)⁻¹ = qP 2 ∧
    ∀ α : Pv ≃* Pv, α ⟨a0, a0_mem⟩ = ⟨evalS alphaWordA, evalS_mem _⟩ →
      α ⟨a1, a1_mem⟩ = ⟨a1, a1_mem⟩ → ∀ j < 28,
        (planeC j)⁻¹ * planeYA α j 0 * planeC j = b1P ^ planeE[j]!.1 * qP 2 ^ planeE[j]!.2.1 ∧
        (planeC j)⁻¹ * planeYA α j (j + 1) * planeC j =
          b1P ^ planeE[j]!.2.2.1 * qP 2 ^ planeE[j]!.2.2.2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := KernelSpor.ONPl.pl_b
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun α h0 h1 => KernelSpor.ONPl.pl_lines α h0 h1⟩

end Certificates

end
