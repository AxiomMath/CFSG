module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Cent3Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
import Certificates.Kernel.HN1408.Cent3Odd
import Certificates.Kernel.HN1408.Cent3WComm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel in
theorem certificate441603 : PrimeFacts 3 [fix3] →
    (∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![pA, pZ, pA * pZ, pB, pZ₁] i) (![pA, pZ, pA * pZ, pB, pZ₁] j)) →
    OddNormalAt (repP fix3) ∧ Perfect60At (repP fix3) ∧ CardTTAt pA pZ pZ₁ (repP fix3) ∧
      WCommAt pA pZ pZ₁ (repP fix3) :=
  fun hpf hnc => ⟨CFSG.KD.HN1408.Cent3.odd_normal hpf, CFSG.KD.HN1408.Cent3.perfect60 hpf,
    CFSG.KD.HN1408.Cent3.card_tT hpf hnc, CFSG.KD.HN1408.Cent3.w_comm hpf hnc⟩

end Certificates
