
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveSound
public import Certificates.Data.HSFiveLocalR
import Certificates.Kernel.MaxD2.HSU35E.HeisEqGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbeddingD2 CFSG.RankThree.Native in
theorem certificate19832 : CFSG.AGLEmbedding.MaxD2.HeisDataEq 5 2 3 12 hs100R hsOR0 ∧
    hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) =
      CFSG.AGLEmbedding.MaxD2.Nsub Certificates.MaxD2Heis.hsFiveDataR [hs100A, hs100B, hs100U] ∧
    Nat.card (CFSG.AGLEmbedding.MaxD2.Nsub Certificates.MaxD2Heis.hsFiveDataR
      [hs100A, hs100B, hs100U]) = 4000 :=
  KernelMaxD2.HSU35E.hsR_heisEq

end Certificates
