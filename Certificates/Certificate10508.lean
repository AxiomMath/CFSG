module

public import CFSG.Sporadic.Th.Max3.RankInputs
import Certificates.Kernel.Th.Rank10508.C2
import CFSG.Certificates.Kernel.Th.SoundnessRank10508

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelTh CertificateChecks.KernelTh.Rank10508 CFSG.KD.ThRk10508

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank in
theorem certificate10508 :
    (∀ a b c d : Fin 9, RkCand (rkTup a b c d) →
      ∃ i : Fin 12, ∀ j : Fin 9, rkTup a b c d j = rkPerm i j) ∧
    RkFacts (rkData ()) :=
  CFSG.KC.Th.Soundness.rank_sound10508 max3Data max3_hA max3_hB max3_ok conj1 LB Ks Es Ws Cl Ts Ds
    hcq hcc hrow hKs hEs hWs hTs h16 h8 h4

end Certificates
