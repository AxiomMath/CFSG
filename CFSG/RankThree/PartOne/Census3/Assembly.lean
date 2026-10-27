module

public import CFSG.RankThree.PartOne.Census3.OpenCases
import CFSG.RankThree.PartOne.Census3.UnitarySixEight
import CFSG.RankThree.PartOne.Census3.Linear
import CFSG.RankThree.PartOne.Census3.Symplectic
import CFSG.RankThree.PartOne.Census3.Alternating
import CFSG.RankThree.PartOne.Census3.Sporadic
import CFSG.RankThree.PartOne.Census3.SporadicCertificates
import CFSG.RankThree.PartTwo.Census.Exceptional.Main
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.Census3

open TauCeti

theorem theoremThreeCase_B_of_open (hspin : SpinRankFour) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) : TheoremThreeCase (.lie ⟨.B r q, hv⟩) := by
  have hr2 : 2 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact theoremThreeCase_B2 q hv
  by_cases h3 : r = 3 ∧ q.p = 2
  · obtain ⟨rfl, hq⟩ := h3
    exact fun G _ _ _ e => TheoremThreeList.of_B3_even hv hq e
  by_cases h4 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hq, hf⟩ := h4
    exact fun G _ _ _ e => TheoremThreeList.of_B4_two hv hq hf e
  exact (excludedIndex_of_four_le (hspin.typeB r q hv hr3 h3 h4)).case

theorem theoremThreeCase_D_of_open (hspin : SpinRankFour) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) : TheoremThreeCase (.lie ⟨.D r q, hv⟩) := by
  by_cases h4 : r = 4 ∧ q.p = 2 ∧ q.exponent = 1
  · obtain ⟨rfl, hq, hf⟩ := h4
    exact fun G _ _ _ e => TheoremThreeList.of_D4_two hv hq hf e
  exact (excludedIndex_of_four_le (hspin.typeD r q hv h4)).case

theorem theoremThreeCase_twistedD_of_open (hspin : SpinRankFour) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) : TheoremThreeCase (.lie ⟨.twistedD r q, hv⟩) := by
  by_cases h4 : r = 4 ∧ q.p = 2
  · obtain ⟨rfl, hq⟩ := h4
    exact fun G _ _ _ e => TheoremThreeList.of_twistedD4_even hv hq e
  exact (excludedIndex_of_four_le (hspin.typeTwistedD r q hv h4)).case

theorem theoremThreeCase_F4_of_open (hexc : ExceptionalRankFour) (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) : TheoremThreeCase (.lie ⟨.F4 q, hv⟩) := by
  by_cases h2 : q.p = 2 ∧ q.exponent = 1
  · exact fun G _ _ _ e => TheoremThreeList.of_F4_two hv h2.1 h2.2 e
  exact (excludedIndex_of_four_le (hexc.f4 q hv h2)).case

theorem theoremThreeCase_G2_of_open (hexc : ExceptionalRankFour) (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) : TheoremThreeCase (.lie ⟨.G2 q, hv⟩) := by
  by_cases hq : q.p = 2
  · exact fun G _ _ _ e => TheoremThreeList.of_G2_even hv hq e
  by_cases hf : q.exponent = 1
  · exact fun G _ _ _ e => TheoremThreeList.of_G2_prime hv hq hf e
  have hf2 : 2 ≤ q.exponent := by
    have := q.exponent_pos
    omega
  exact (excludedIndex_of_four_le (hexc.g2 q hv hq hf2)).case

theorem theoremThreeCase_trialityD4_of_open (hexc : ExceptionalRankFour) (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) : TheoremThreeCase (.lie ⟨.trialityD4 q, hv⟩) := by
  by_cases hq : q.p = 2
  · exact fun G _ _ _ e => TheoremThreeList.of_trialityD4_even hv hq e
  exact (excludedIndex_of_four_le (hexc.trialityD4 q hv hq)).case

theorem theoremThreeCase_reeG2_of_open (hexc : ExceptionalRankFour) (m : ℕ)
    (hv : (LieTypeIndex.reeG2 m).Valid) : TheoremThreeCase (.lie ⟨.reeG2 m, hv⟩) := by
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · exact fun G _ _ _ e => TheoremThreeList.of_reeG2_one hv e
  · exact (excludedIndex_of_four_le (hexc.reeG2 m hv hm2)).case

theorem theoremThreeCase_lie_of_open (hspin : SpinRankFour) (hexc : ExceptionalRankFour)
    (d : ValidLieTypeIndex) : TheoremThreeCase (.lie d) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact theoremThreeCase_A r q hv
  | twistedA r q => exact theoremThreeCase_twistedA localRankThreeU68 r q hv
  | B r q => exact theoremThreeCase_B_of_open hspin r q hv
  | C r q => exact theoremThreeCase_C r q hv
  | D r q => exact theoremThreeCase_D_of_open hspin r q hv
  | twistedD r q => exact theoremThreeCase_twistedD_of_open hspin r q hv
  | E6 q => exact (excludedIndex_of_four_le (hexc.e6 q hv)).case
  | E7 q => exact (excludedIndex_of_four_le (hexc.e7 q hv)).case
  | E8 q => exact (excludedIndex_of_four_le (hexc.e8 q hv)).case
  | F4 q => exact theoremThreeCase_F4_of_open hexc q hv
  | G2 q => exact theoremThreeCase_G2_of_open hexc q hv
  | twistedE6 q => exact (excludedIndex_of_four_le (hexc.twistedE6 q hv)).case
  | trialityD4 q => exact theoremThreeCase_trialityD4_of_open hexc q hv
  | suzuki m => exact fun G _ _ _ e => TheoremThreeList.of_suzuki hv e
  | reeG2 m => exact theoremThreeCase_reeG2_of_open hexc m hv
  | reeF4 m => exact fun G _ _ _ e => TheoremThreeList.of_reeF4 hv e
  | tits => exact fun G _ _ _ e => TheoremThreeList.of_tits hv e

theorem theorem_three_catalog_of_open (hspin : SpinRankFour) (hexc : ExceptionalRankFour)
    (hB : RankFourBabyMonster) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.IsKGroup G)
    (he : CFSG.twoLocalOddRank G ≤ 3) : TheoremThreeList G := by
  refine theorem_three_of_cases (fun i => ?_) G ⟨inferInstance, hnonab, hK, he⟩
  cases i with
  | cyclic p hp => exact theoremThreeCase_cyclic p hp
  | alternating n hn => exact theoremThreeCase_alternating n hn
  | lie d => exact theoremThreeCase_lie_of_open hspin hexc d
  | sporadic s =>
    exact theoremThreeCase_sporadic_of excludedIndex_Co1 excludedIndex_Fi23 hB s

theorem theorem_three_catalog_of_spin (hspin : SpinRankFour) (hB : RankFourBabyMonster)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.IsKGroup G) (he : CFSG.twoLocalOddRank G ≤ 3) : TheoremThreeList G :=
  theorem_three_catalog_of_open hspin CFSG.RankThree.PartTwo.Census.Exceptional.exceptionalRankFour
    hB G hnonab hK he

end CFSG.RankThree.PartOne.Census3
