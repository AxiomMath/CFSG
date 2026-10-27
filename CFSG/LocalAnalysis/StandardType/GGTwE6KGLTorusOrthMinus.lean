module

public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly

theorem largeEvenLabelAll_torusLift_orthMinus_threeFive {lab : LargeEvenLabel}
    (htag : lab.tag = .twD) (h3 : 3 ∣ 2 ^ lab.n + 1) (h6 : 6 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
  (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three
    ⟨by omega, Or.inl ⟨htag, h3⟩⟩).mono fun _ _ _ _ h =>
      ggTorusLift_mono Nat.prime_three h.2 (by omega)

end CFSG.StandardType.SCFourCover

end
