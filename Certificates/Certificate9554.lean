module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import Certificates.Kernel.Sporadic.Fi22.C9554Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Co2 in
theorem certificate9554 : ∀ G₁ G₂ : Equiv.Perm (Fin 3510), Rep 3510 g1A G₁ → Rep 3510 g2A G₂ →
    1045094400 ≤ Nat.card (Subgroup.closure ({G₁, G₂} : Set (Equiv.Perm (Fin 3510)))) :=
  fun _ _ h₁ h₂ => KernelSpor.Fi22C9554.card_ge h₁ h₂

end Certificates
