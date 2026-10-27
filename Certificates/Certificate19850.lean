
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
import Certificates.Kernel.MaxD2.HSU35E.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2 in
theorem certificate19850 : Nat.card hsOUA = 126000 ∧
    hsOUA ⊓ Subgroup.centralizer ({hsOT} : Set (Equiv.Perm (Fin 100))) = Subgroup.zpowers hsOT :=
  ⟨KernelMaxD2.HSU35E.hsU35E_card, KernelMaxD2.HSU35E.hsU35E_cent⟩

end Certificates
