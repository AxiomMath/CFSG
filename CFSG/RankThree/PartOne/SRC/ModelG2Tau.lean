module

public import CFSG.RankThree.PartOne.SRC.ModelG2
public import CFSG.RankThree.PartOne.SRC.ModelG2Two
import CFSG.Adapters.TauCetiExceptional.BridgeG2

public section

namespace CFSG.RankThree.PartOne.SRC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Census.Carrier TauCeti


theorem rankFourCover_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2)
    (he : 4 ≤ q.exponent) : RankFourCover q.p (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
  exact rankFourCover_of_mulEquiv b.symm
    (rankFourCover_of_mulEquiv (adjointQuotientG2Equiv (GaloisField q.p q.exponent))
      (rankFourCover_adjointG2 (K := GaloisField q.p q.exponent) (hK.trans (PrimePower.card_def q))
        hp2 he))

theorem rankFourCover_G2_two (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p ≠ 2)
    (he : 2 ≤ q.exponent) (h9 : q.card ≠ 9) :
    RankFourCover q.p (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
  exact rankFourCover_of_mulEquiv b.symm
    (rankFourCover_of_mulEquiv (adjointQuotientG2Equiv (GaloisField q.p q.exponent))
      (rankFourCover_adjointG2_two (K := GaloisField q.p q.exponent)
        (hK.trans (PrimePower.card_def q)) hp2 he (by rw [hK]; exact h9)))

end CFSG.RankThree.PartOne.SRC
