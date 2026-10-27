module

public import CFSG.Sporadic.Fi24.PtGraph
import Certificates.Kernel.Sporadic.Fi24P7.Final

public section

open CFSG.Sporadic.Fi24

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi24 in
theorem certificate214036 : ∃ s : Fin 5 → GL (Fin 781) (ZMod 3),
    (∀ i, s i ∈ seedGrp ∧ s i ^ 3 = 1 ∧ s i ≠ 1) ∧
    Nat.card (ptFix (s 0)) = 3240 ∧ Nat.card (ptFix (s 1)) = 1485 ∧
    Nat.card (ptFix (s 2)) = 378 ∧ Nat.card (ptFix (s 3)) = 162 ∧ Nat.card (ptFix (s 4)) = 0 ∧
    ∀ i : Fin 5, i = 0 ∨ i = 2 ∨ i = 4 → ∃ a ∈ seedGrp, ∃ b ∈ seedGrp,
      a * s i = s i * a ∧ b * s i = s i * b ∧ orderOf a = 7 ∧ orderOf b = 7 ∧
      81 ∣ Nat.card (Subgroup.closure ({a, b} : Set (GL (Fin 781) (ZMod 3)))) := KernelFi24P7.fi24_three_pairs

end Certificates

end

end
