module

public import CFSG.Sporadic.Fi24.PtGraph
import Certificates.Kernel.Sporadic.Fi24F3d.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate10136 : ∃ e ∈ seedGrp, ∃ f ∈ seedGrp, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 →
      Nat.card (ptFix (e ^ a * f ^ b)) = 36 ∧
      ∃ P : Fin 8 → Submodule (ZMod 3) (Fin 781 → ZMod 3), (∀ i, P i ∈ ptFix (e ^ a * f ^ b)) ∧
        (∀ i j : Fin 8, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j)) ∧
        (∀ i j : Fin 8, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) := KernelFi24F3d.fi24_five_chain

end Certificates

end
