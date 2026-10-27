module

public import CFSG.RankThree.PartOne.N143.SectionListProof
public import CFSG.RankThree.PartOne.N143.LieThree
public import CFSG.RankThree.PartOne.N143.LieHigh
public import CFSG.RankThree.PartOne.N143.LieE6
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

@[expose] def NoOddCentralCoverFor (P : CFSGIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsKGroup Y → Group.IsPerfect Y → CFSG.Assembly.evenRank Y ≤ 3 →
    ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ φ : Y →* S, Function.Surjective φ → φ.ker ≤ center Y → IsPGroup 3 φ.ker → 3 ∣ Nat.card φ.ker →
        (∃ i : CFSGIndex, P i ∧ Nonempty (S ≃* i.Group)) → False

theorem NoOddCentralCoverFor.rank {P : CFSGIndex → Prop} (h : NoOddCentralCoverFor P) :
    OddCentralCoverRank3For P :=
  fun Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd hP =>
    (h Y hK hperf he S hnonab φ hφ hcent h3 h3dvd hP).elim

theorem NoOddCentralCoverFor.list {P : CFSGIndex → Prop} (h : NoOddCentralCoverFor P) :
    OddCentralCoverList3For P :=
  fun Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd hP =>
    (h Y hK hperf he S hnonab φ hφ hcent h3 h3dvd hP).elim

theorem primePower_eq_three {q : PrimePower} (h : q.card = 3) : q.p = 3 ∧ q.exponent = 1 := by
  rw [PrimePower.card_def] at h
  have hp : q.p ∣ 3 := by
    have : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [h] at this
    exact this
  have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hp
  refine ⟨hp3, ?_⟩
  rw [hp3] at h
  have : (3 : ℕ) ^ q.exponent = 3 ^ 1 := by rw [h]; norm_num
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this

theorem oddCentralCoverList3For_lieSmall : OddCentralCoverList3For IsLieSmallIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsLieSmallIndex])
  | alternating n hn => exact absurd hi (by simp [IsLieSmallIndex])
  | sporadic s => exact absurd hi (by simp [IsLieSmallIndex])
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | twistedA r q =>
      obtain ⟨hr, hq3⟩ : r = 3 ∧ q.card = 3 := hi
      subst hr
      obtain ⟨hp3, hexp⟩ := primePower_eq_three hq3
      exact Census3.TheoremThreeList.of_twistedA3_prime hv (by omega) hexp e
    | G2 q =>
      have hq3 : q.card = 3 := hi
      obtain ⟨hp3, hexp⟩ := primePower_eq_three hq3
      exact Census3.TheoremThreeList.of_G2_prime hv (by omega) hexp e
    | A r q => exact absurd hi (by simp [IsLieSmallIndex])
    | B r q => exact absurd hi (by simp [IsLieSmallIndex])
    | C r q => exact absurd hi (by simp [IsLieSmallIndex])
    | D r q => exact absurd hi (by simp [IsLieSmallIndex])
    | twistedD r q => exact absurd hi (by simp [IsLieSmallIndex])
    | E6 q => exact absurd hi (by simp [IsLieSmallIndex])
    | E7 q => exact absurd hi (by simp [IsLieSmallIndex])
    | E8 q => exact absurd hi (by simp [IsLieSmallIndex])
    | F4 q => exact absurd hi (by simp [IsLieSmallIndex])
    | twistedE6 q => exact absurd hi (by simp [IsLieSmallIndex])
    | trialityD4 q => exact absurd hi (by simp [IsLieSmallIndex])
    | suzuki m => exact absurd hi (by simp [IsLieSmallIndex])
    | reeG2 m => exact absurd hi (by simp [IsLieSmallIndex])
    | reeF4 m => exact absurd hi (by simp [IsLieSmallIndex])
    | tits => exact absurd hi (by simp [IsLieSmallIndex])

theorem oddCentralCoverList3For_lie_of_parts (hTC : RankThree.PartTwo.Sec4.Census.TripleCoverLie)
    (hThree : OddCentralCoverList3For IsLieThreeIndex) (hHigh : OddCentralCoverList3For IsLieHighIndex)
    (hSmall : OddCentralCoverList3For IsLieSmallIndex) (hO7 : OddCentralCoverList3For IsLieO7Index)
    (hE6 : OddCentralCoverList3For IsLieE6Index) : OddCentralCoverList3For IsLieIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsLieIndex])
  | alternating n hn => exact absurd hi (by simp [IsLieIndex])
  | sporadic s => exact absurd hi (by simp [IsLieIndex])
  | lie d =>
    obtain ⟨hker, hYq, ⟨hcongr⟩⟩ := central_cover_quasisimple hperf hnonab φ hφ hcent
    have h3Z : 3 ∣ Nat.card (Subgroup.center Y) := by rw [hker]; exact h3dvd
    have htc := hTC d Y ⟨hYq, h3Z, ⟨hcongr.trans e⟩⟩
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      have hr1 : 1 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
      have htc' : 3 ∣ r + 1 ∧ 3 ∣ q.card - 1 := htc
      have hr : r = 2 ∨ 5 ≤ r := by
        have := htc'.1
        omega
      rcases hr with h2r | h5
      · exact hThree Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
          ⟨CFSGIndex.lie ⟨.A r q, hv⟩, ⟨h2r, htc'.2⟩, ⟨e⟩⟩
      · exact hHigh Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
          ⟨CFSGIndex.lie ⟨.A r q, hv⟩, ⟨h5, htc'⟩, ⟨e⟩⟩
    | twistedA r q =>
      have hr2 : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
      have htc' : (3 ∣ r + 1 ∧ 3 ∣ q.card + 1) ∨ (r = 3 ∧ q.card = 3) := htc
      rcases htc' with ⟨h1, h2⟩ | ⟨hr3, hq3⟩
      · have hr : r = 2 ∨ 5 ≤ r := by omega
        rcases hr with h2r | h5
        · exact hThree Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
            ⟨CFSGIndex.lie ⟨.twistedA r q, hv⟩, ⟨h2r, h2⟩, ⟨e⟩⟩
        · exact hHigh Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
            ⟨CFSGIndex.lie ⟨.twistedA r q, hv⟩, ⟨h5, h1, h2⟩, ⟨e⟩⟩
      · exact hSmall Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
          ⟨CFSGIndex.lie ⟨.twistedA r q, hv⟩, ⟨hr3, hq3⟩, ⟨e⟩⟩
    | B r q =>
      have htc' : r = 3 ∧ q.card = 3 := htc
      exact hO7 Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.lie ⟨.B r q, hv⟩, htc', ⟨e⟩⟩
    | C r q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | D r q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | twistedD r q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | E6 q =>
      have htc' : 3 ∣ q.card - 1 := htc
      exact hE6 Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.lie ⟨.E6 q, hv⟩, htc', ⟨e⟩⟩
    | E7 q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | E8 q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | F4 q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | G2 q =>
      have htc' : q.card = 3 := htc
      exact hSmall Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.lie ⟨.G2 q, hv⟩, htc', ⟨e⟩⟩
    | twistedE6 q =>
      have htc' : 3 ∣ q.card + 1 := htc
      exact hE6 Y hK hperf he S hnonab φ hφ hcent h3 h3dvd
        ⟨CFSGIndex.lie ⟨.twistedE6 q, hv⟩, htc', ⟨e⟩⟩
    | trialityD4 q => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | suzuki m => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | reeG2 m => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | reeF4 m => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])
    | tits => exact absurd htc (by simp [RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex])

theorem oddCentralCoverList3For_lie (hT : ThreeCat) (hTC : RankThree.PartTwo.Sec4.Census.TripleCoverLie)
    (hHighEven : NoOddCentralCoverFor IsLieHighEvenIndex) (hO7 : NoOddCentralCoverFor IsLieO7Index)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo)
    (hB : CFSG.TauCetiBridge.Even.ChevalleyBridgesAll) : OddCentralCoverList3For IsLieIndex :=
  oddCentralCoverList3For_lie_of_parts hTC
    (oddCentralCoverList3For_of_rank hT oddCentralCoverRank3For_lieThree)
    (oddCentralCoverList3For_of_rank hT (oddCentralCoverRank3For_lieHigh hHighEven.rank))
    oddCentralCoverList3For_lieSmall hO7.list
    (oddCentralCoverList3For_of_rank hT (oddCentralCoverRank3For_lieE6 hE hB))

end CFSG.RankThree.PartOne.N143
