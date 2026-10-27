module

public import CFSG.Sporadic.Fi24.PtGraph
import Certificates.Kernel.Sporadic.Fi24F3d.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate10135 : ∃ y ∈ seedGrp, ∃ e ∈ seedGrp, y ^ 7 = 1 ∧ y ≠ 1 ∧ e ^ 5 = 1 ∧ e ≠ 1 ∧ e * y = y * e ∧
    ∃ P : Fin 6 → Submodule (ZMod 3) (Fin 781 → ZMod 3), (∀ i, P i ∈ ptFix y) ∧
      (∀ i j : Fin 6, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j)) ∧
      (∀ i j : Fin 6, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) := KernelFi24F3d.fi24_seven_chain

end Certificates

end
