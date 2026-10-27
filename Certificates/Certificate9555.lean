module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import Certificates.Kernel.Sporadic.Fi22.Or9555Main

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 CFSG.Certificates in
open scoped Pointwise in
theorem certificate9555 : ∀ G₁ G₂ : Equiv.Perm (Fin 3510), Rep 3510 g1A G₁ → Rep 3510 g2A G₂ →
    (G₁ • finSet 3510 s0List = finSet 3510 s0List ∧
      G₂ • finSet 3510 s0List = finSet 3510 s0List) ∧
    ∀ A B : Equiv.Perm (Fin 3510), Rep 3510 (evalW [1]) A → Rep 3510 (evalW [2]) B →
      ∃ E : Fin 4 → Set (Set (Fin 3510)), (∀ j, (E j).Finite) ∧
        (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        (∀ j, ∀ S ∈ E j, ∃ g ∈ Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510))),
          S = g • ((![1, A, B, B * A] : Fin 4 → Equiv.Perm (Fin 3510)) j •
            finSet 3510 s0List)) ∧
        (∀ j, (E j).ncard = (![1, 1575, 22400, 37800] : Fin 4 → ℕ) j) :=
  KernelSpor.Or9555.orbit_pieces

end Certificates
