
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveSound
import Certificates.Kernel.MaxD2.HSU35E.HeisEqGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2 CFSG.RankThree.Native in
theorem certificate19831 : CFSG.AGLEmbedding.MaxD2.HeisDataEq 5 2 3 12 hs100P hsOR0 ∧
    hsON0 = hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∧
    Nat.card hsON0 = 2000 :=
  KernelMaxD2.HSU35E.hsP_heisEq

end Certificates
