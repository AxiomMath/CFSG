module

public import CFSG.RankThree.PartOne.N143.LieLeaves
import CFSG.RankThree.PartOne.N143.HeisenbergThree
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.N143.SectionRankSplit

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti Subgroup Matrix

theorem evenRank_le_three_of_localRank_three {Y S : Type} [Group Y] [Finite Y] [Group S] [Finite S]
    (φ : Y →* S) (hφ : Function.Surjective φ) (h3 : IsPGroup 3 φ.ker)
    (he : CFSG.Assembly.evenRank Y ≤ 3) (hS3 : localRank 3 S ≤ 3) :
    CFSG.Assembly.evenRank S ≤ 3 := by
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hr3 : r = 3
  · subst hr3
    exact hS3
  · have hnd : ¬ r ∣ Nat.card φ.ker := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h3
      rw [hn]
      intro h
      exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h))
    let eS : (Y ⧸ φ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    calc localRank r S = localRank r (Y ⧸ φ.ker) :=
          (CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv eS hr).symm
      _ ≤ localRank r Y := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 φ.ker hnd
      _ ≤ CFSG.Assembly.evenRank Y := CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2
      _ ≤ 3 := he

theorem ne_three_of_dvd_pow_sub_one_or_add_one {p f : ℕ} (hf : 1 ≤ f)
    (h : 3 ∣ p ^ f - 1 ∨ 3 ∣ p ^ f + 1) : p ≠ 3 := by
  rintro rfl
  have h3pow : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  rcases h with h | h
  · have hpos : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    have := Nat.dvd_sub h3pow h
    have e : 3 ^ f - (3 ^ f - 1) = 1 := by omega
    rw [e] at this
    omega
  · have := (Nat.dvd_add_right h3pow).mp h
    omega

theorem three_ne_zero_galoisField {p f : ℕ} [Fact p.Prime] (hp : p ≠ 3) :
    (3 : GaloisField p f) ≠ 0 := by
  intro h0
  have : ((3 : ℕ) : GaloisField p f) = 0 := by exact_mod_cast h0
  have hdvd := (CharP.cast_eq_zero_iff (GaloisField p f) p 3).1 this
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 hdvd)

theorem oddCentralCoverRank3For_lieThree : OddCentralCoverRank3For IsLieThreeIndex := by
  intro Y _ _ hK hperf he S _ _ _ hnonab φ hφ hcent h3 h3dvd ⟨i, hi, ⟨e⟩⟩
  refine evenRank_le_three_of_localRank_three φ hφ h3 he ?_
  cases i with
  | cyclic p hp => exact absurd hi (by simp [IsLieThreeIndex])
  | alternating n hn => exact absurd hi (by simp [IsLieThreeIndex])
  | sporadic s => exact absurd hi (by simp [IsLieThreeIndex])
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      obtain ⟨hr2, hq3⟩ : r = 2 ∧ 3 ∣ q.card - 1 := hi
      subst hr2
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
        (Or.inl (by simpa [PrimePower.card_def] using hq3))
      have hK3 : (3 : GaloisField q.p q.exponent) ≠ 0 := three_ne_zero_galoisField hp3
      let eP := CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 2 q hv
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv (e.trans eP) Nat.prime_three]
      exact localRank_three_le_three_projSL hK3
    | twistedA r q =>
      obtain ⟨hr2, hq3⟩ : r = 2 ∧ 3 ∣ q.card + 1 := hi
      subst hr2
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hp3 : q.p ≠ 3 := ne_three_of_dvd_pow_sub_one_or_add_one q.exponent_pos
        (Or.inr (by simpa [PrimePower.card_def] using hq3))
      have hK3 : (3 : GaloisField q.p (2 * q.exponent)) ≠ 0 := three_ne_zero_galoisField hp3
      let eP := CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv
      rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv (e.trans eP) Nat.prime_three]
      exact localRank_three_le_three_projSU q.p q.exponent hK3
    | B r q => exact absurd hi (by simp [IsLieThreeIndex])
    | C r q => exact absurd hi (by simp [IsLieThreeIndex])
    | D r q => exact absurd hi (by simp [IsLieThreeIndex])
    | twistedD r q => exact absurd hi (by simp [IsLieThreeIndex])
    | E6 q => exact absurd hi (by simp [IsLieThreeIndex])
    | E7 q => exact absurd hi (by simp [IsLieThreeIndex])
    | E8 q => exact absurd hi (by simp [IsLieThreeIndex])
    | F4 q => exact absurd hi (by simp [IsLieThreeIndex])
    | G2 q => exact absurd hi (by simp [IsLieThreeIndex])
    | twistedE6 q => exact absurd hi (by simp [IsLieThreeIndex])
    | trialityD4 q => exact absurd hi (by simp [IsLieThreeIndex])
    | suzuki m => exact absurd hi (by simp [IsLieThreeIndex])
    | reeG2 m => exact absurd hi (by simp [IsLieThreeIndex])
    | reeF4 m => exact absurd hi (by simp [IsLieThreeIndex])
    | tits => exact absurd hi (by simp [IsLieThreeIndex])

end CFSG.RankThree.PartOne.N143
