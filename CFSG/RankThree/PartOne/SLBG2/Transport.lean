module

public import CFSG.RankThree.PartOne.SRC.Nine
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.Adapters.TauCetiExceptional.BridgeG2

public section

namespace CFSG.RankThree.PartOne.SLBG2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartTwo.Census.Carrier TauCeti
  CFSG.RankThree.PartOne.SRC

theorem p_eq_three_of_card_eq_nine (q : PrimePower) (h9 : q.card = 9) : q.p = 3 := by
  have hd : q.p ∣ 3 ^ 2 := by
    have : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← PrimePower.card_def, h9] at this
    norm_num
    exact this
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 (q.prime_p.dvd_of_dvd_pow hd)


theorem rankFourCover_G2_nine_of_native
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 3], Nat.card K = 9 →
      RankFourCover 3 (adjointGroup Tag.G2 K))
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (h9 : q.card = 9) :
    RankFourCover 3 (CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have hp3 : q.p = 3 := p_eq_three_of_card_eq_nine q h9
  have hp2 : q.p ≠ 2 := by rw [hp3]; norm_num
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  have hchar : CharP (GaloisField q.p q.exponent) 3 := hp3 ▸ (inferInstance : CharP _ q.p)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 (GaloisField q.p q.exponent) hK
  exact rankFourCover_of_mulEquiv b.symm
    (rankFourCover_of_mulEquiv (adjointQuotientG2Equiv (GaloisField q.p q.exponent))
      (h (GaloisField q.p q.exponent) (hK.trans h9)))

theorem rankFourCoverG2_of_native
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 3], Nat.card K = 9 →
      RankFourCover 3 (adjointGroup Tag.G2 K)) : RankFourCoverG2 := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    rename_i q
    exact rankFourCover_G2_nine_of_native h q hv hi
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SLBG2
