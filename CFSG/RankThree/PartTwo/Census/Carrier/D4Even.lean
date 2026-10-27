module

public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenRank
public import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.Adapters.TauCetiExceptional.EvenD4

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

theorem excluded433_trialityD4_even (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hp : q.p = 2) : Excluded433 (.lie ⟨.trialityD4 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK : Nat.card (GaloisField 2 (q.exponent * 3)) = (2 ^ q.exponent) ^ 3 := by
    rw [GaloisField.card 2 (q.exponent * 3) (by omega), pow_mul]
  have hKq : Nat.card (GaloisField 2 (q.exponent * 3)) = q.card ^ 3 := by
    rw [hK, PrimePower.card_def, hp]
  have hσ : ∀ x : GaloisField 2 (q.exponent * 3),
      iterateFrobenius (GaloisField 2 (q.exponent * 3)) 2 q.exponent x = x ^ 2 ^ q.exponent :=
    fun x => by rw [iterateFrobenius_def]
  have hσq : ∀ x : GaloisField 2 (q.exponent * 3),
      iterateFrobenius (GaloisField 2 (q.exponent * 3)) 2 q.exponent x = x ^ q.card := fun x => by
    rw [hσ, PrimePower.card_def, hp]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hp
    (GaloisField 2 (q.exponent * 3)) hKq _ hσq
  exact hG.false_of_localRank_three_le_two (e.trans b.symm)
    (Carrier.D4Even.localRank_three_derivedCentralQuotient q.exponent hf hK _ hσ)

end CFSG.RankThree.PartTwo.Census
