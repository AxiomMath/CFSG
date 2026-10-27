module

public import CFSG.RankThree.PartOne.N143.LieLeaves
public import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.RankThree.PartOne.N143.LieHigh
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup CFSG.Blueprint

theorem oddCentralCoverRank3For_lieE6 (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) : OddCentralCoverRank3For IsLieE6Index := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  exfalso
  obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
  have he' : CFSG.twoLocalOddRank Y ≤ 3 := by
    rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact he
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsLieE6Index])
  | alternating n hn => exact absurd hi (by simp [IsLieE6Index])
  | sporadic s => exact absurd hi (by simp [IsLieE6Index])
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | E6 q =>
      have hq3 : 3 ∣ q.card - 1 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', PrimePower.card_def]
      obtain ⟨br⟩ := hB.e6 q hv (GaloisField q.p q.exponent) hcard
      have hmod : ChevalleyExceptionalModel (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y)) .E6
          q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p q.exponent, inferInstance, inferInstance,
          by rw [hcard, PrimePower.card_def],
          ⟨(((topCenterEquiv Y).trans hcongr).trans e).trans br.symm⟩⟩
      obtain ⟨-, hp2, hf1⟩ := hE Y he' ⊤ q.p q.exponent q.prime_p q.exponent_pos .E6
        (Or.inl rfl) hmod
      have : q.card = 2 := by rw [PrimePower.card_def, hp2, hf1]; norm_num
      rw [this] at hq3
      omega
    | twistedE6 q =>
      have hq3 : 3 ∣ q.card + 1 := hi
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hcard : Nat.card (GaloisField q.p (q.exponent * 2)) = q.card ^ 2 := by
        rw [GaloisField.card q.p (q.exponent * 2) (by have := q.exponent_pos; omega),
          PrimePower.card_def, pow_mul]
      obtain ⟨br⟩ := hB.twistedE6 q hv (GaloisField q.p (q.exponent * 2)) hcard
        (iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent)
        (fun x => by rw [iterateFrobenius_def, PrimePower.card_def])
      have hmod : ChevalleyExceptionalModel (↥(⊤ : Subgroup Y) ⧸ center ↥(⊤ : Subgroup Y))
          .twistedE6 q.p q.exponent :=
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent * 2), inferInstance,
          inferInstance, by rw [hcard, PrimePower.card_def]; rfl,
          iterateFrobenius (GaloisField q.p (q.exponent * 2)) q.p q.exponent,
          fun c => by rw [iterateFrobenius_def],
          ⟨(((topCenterEquiv Y).trans hcongr).trans e).trans br.symm⟩⟩
      obtain ⟨h, -, -⟩ := hE Y he' ⊤ q.p q.exponent q.prime_p q.exponent_pos .twistedE6
        (Or.inr (Or.inr (Or.inr rfl))) hmod
      exact absurd h (by decide)
    | A r q => exact absurd hi (by simp [IsLieE6Index])
    | twistedA r q => exact absurd hi (by simp [IsLieE6Index])
    | B r q => exact absurd hi (by simp [IsLieE6Index])
    | C r q => exact absurd hi (by simp [IsLieE6Index])
    | D r q => exact absurd hi (by simp [IsLieE6Index])
    | twistedD r q => exact absurd hi (by simp [IsLieE6Index])
    | E7 q => exact absurd hi (by simp [IsLieE6Index])
    | E8 q => exact absurd hi (by simp [IsLieE6Index])
    | F4 q => exact absurd hi (by simp [IsLieE6Index])
    | G2 q => exact absurd hi (by simp [IsLieE6Index])
    | trialityD4 q => exact absurd hi (by simp [IsLieE6Index])
    | suzuki m => exact absurd hi (by simp [IsLieE6Index])
    | reeG2 m => exact absurd hi (by simp [IsLieE6Index])
    | reeF4 m => exact absurd hi (by simp [IsLieE6Index])
    | tits => exact absurd hi (by simp [IsLieE6Index])

end CFSG.RankThree.PartOne.N143
