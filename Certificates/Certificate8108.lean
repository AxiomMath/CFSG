module

public import CFSG.RankThree.Co2.JFacts
import Certificates.Kernel.Co2J.Facts
import Certificates.Kernel.Co2Fuse.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Co2 in
theorem certificate8108 : (∀ x ∈ matGrp sylWords, x ^ 32 = 1) ∧ Nat.card (matGrp sylWords) = 2 ^ 18 ∧
    matGrp jWords ≤ matGrp sylWords :=
  ⟨KernelSpor.Co2J.tFacts.pow,
    le_antisymm KernelSpor.Co2Fuse.T_card_le KernelSpor.Co2J.tFacts.card,
    KernelSpor.Co2J.jFacts.le⟩

end Certificates
