module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylowGroup
import Certificates.Kernel.D4Syl.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Open in
theorem certificate9415 : Nat.card sylowGroup = 81 ∧
    (∀ E : Subgroup (GL (Fin 8) GF8), E ≤ sylowGroup → IsElemAbelian 3 E → Nat.card E ≤ 9) ∧
    ∀ g ∈ sylowGroup, ∃ x ∈ sylowElems,
      ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x :=
  ⟨KernelD4Syl.card_closure_eq, KernelD4Syl.card_le_nine, KernelD4Syl.exists_mem_sylowElems⟩

end Certificates
