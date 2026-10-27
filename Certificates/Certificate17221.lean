module

public import CFSG.Sporadic.Fi24.PtGraph
import Certificates.Kernel.Sporadic.Fi24F3d.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate17221 : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      Nat.card (ptFix (e ^ a * f ^ b)) = 36 := KernelFi24F3d.fi24_five_card

end Certificates

end
