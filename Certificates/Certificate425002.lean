module

public import CFSG.RankThree.PartOne.KS.HNFiveMatrix
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor
import Certificates.Kernel.HN.PcFive.Witness
public import CFSG.RankThree.PartOne.KS.HNFiveBasic
public import Certificates.Certificate113

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KS.HNFive in
theorem certificate425002 : ∀ {G : Type} [Group G] [Finite G] {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G}
    {BU : Fin k → GL (Fin 4) (ZMod 5)} {cr : Fin k → Fin 4 → ℕ} {m : ℕ},
    Nat.card G = 5 ^ 6 * m → ¬ 5 ∣ m → Rel q z x r Mm XU cx BU cr →
      ∀ s : G, orderOf s = 5 → CFSG.LocalAnalysis.RankFourTheoremC.RankThreeWitness 5 s :=
  fun hcard hm hR => KernelHN.PcFive.hnFiveWitness hcard hm hR

end Certificates
