module

public import CFSG.RankThree.Native.ONTripleA6Inputs
import Certificates.Kernel.Misc.Perm.A6

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple Equiv Equiv.Perm in
theorem certificate8136 : (Nat.card (Subgroup.closure {g | g ∈ [sK1, sK2]}) = 360)
    ∧ (Equiv.Perm.sign sK1 = 1 ∧ Equiv.Perm.sign sK2 = 1)
    ∧ (∀ j : ℕ, j < 2 → ∀ t : Perm (Fin 6), Equiv.Perm.sign t = 1 →
        t ^ 4 = 1 → t ≠ 1 →
          (∃ m < 3, ∃ i < 3, t = sV j m i) ∨ (cand1 (sY j) t).any (fun u => u ^ 4 != 1))
    ∧ (∀ j : ℕ, j < 2 → ∀ m : ℕ, m < 3 → ∀ s : Perm (Fin 6),
        Equiv.Perm.sign s = 1 → s ^ 4 = 1 → s ≠ 1 → (∀ i < 3, s ≠ sV j m i) →
          (cand2 (sY j) s [1, sV j m 0, sV j m 1, sV j m 2]).any (fun u => u ^ 4 != 1)) := KernelMisc.A6.facts

end Certificates
