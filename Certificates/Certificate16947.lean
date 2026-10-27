module

public import CFSG.Sporadic.Fi24.PtGraph
import Certificates.Kernel.Sporadic.Fi24F3d.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate16947 : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      (ptFix (e ^ a * f ^ b)).Nonempty ∧
      (∀ V ∈ ptFix (e ^ a * f ^ b), ∃ W ∈ ptFix (e ^ a * f ^ b), W ≠ V ∧ PtAdj V W) ∧
      (∀ V ∈ ptFix (e ^ a * f ^ b), ∀ W ∈ ptFix (e ^ a * f ^ b), V ≠ W → ¬ PtAdj V W →
        ∃ Z ∈ ptFix (e ^ a * f ^ b), PtAdj Z V ∧ PtAdj Z W) := KernelFi24F3d.fi24_five_graph

end Certificates

end
