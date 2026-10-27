module

public import CFSG.RankThree.PartOne.N143.SecRankRest
public import CFSG.RankThree.PartOne.SLB4A.IndexExc

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly TauCeti

@[expose] def IsTwoPowFiveUnion (i : CFSGIndex) : Prop :=
  IsTypeAIndex i ∨ IsTypeTwistedAIndex i ∨ IsTypeCIndex i ∨ IsTypeBEvenIndex i ∨
    IsTypeBOddIndex i ∨ IsTypeDIndex i ∨ IsTypeTwistedDIndex i ∨ IsTypeEOddIndex i ∨
    IsTypeEEvenIndex i ∨ IsTypeF4OddIndex i ∨ IsTypeF4EvenIndex i ∨ IsTypeTwistedE6OddIndex i ∨
    IsTypeTwistedE6EvenIndex i

theorem card_mod_two_of_ne_two (q : PrimePower) (hp : q.p ≠ 2) : q.card % 2 = 1 := by
  rw [PrimePower.card_def]
  exact Nat.odd_iff.1 ((q.prime_p.eq_two_or_odd'.resolve_left hp).pow)

theorem isLieTwoPowFiveIndex_cases {i : CFSGIndex} (h : N143.IsLieTwoPowFiveIndex i) :
    IsTwoPowFiveUnion i := by
  obtain ⟨⟨hlie, hlisted, hhard⟩, hlow⟩ := h
  cases i with
  | cyclic p hp => exact hlie.elim
  | alternating n hn => exact hlie.elim
  | sporadic s => exact hlie.elim
  | lie d =>
    obtain ⟨d, hv⟩ := d
    have hv' := (LieTypeIndex.valid_iff _).1 hv
    cases d with
    | A r q =>
      have h2 := card_mod_two_of_ne_two q
      have he := q.exponent_pos
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      have hr : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      refine Or.inl ?_
      show (q.p = 2 ∧ 4 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 1) ∨ (q.p ≠ 2 ∧ 6 ≤ r)
      by_cases hp : q.p = 2
      · simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
      · simp only [hp, ne_eq, not_false_eq_true, false_and, and_false, or_false, true_and, false_or,
          and_true] at hlisted hhard hlow ⊢
        omega
    | twistedA r q =>
      have h2 := card_mod_two_of_ne_two q
      have he := q.exponent_pos
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      have hr : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      refine Or.inr (Or.inl ?_)
      show (q.p = 2 ∧ 5 ≤ r) ∨ (q.p ≠ 2 ∧ r = 5 ∧ q.card % 4 = 3) ∨ (q.p ≠ 2 ∧ 6 ≤ r)
      by_cases hp : q.p = 2
      · simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
      · simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
    | B r q =>
      have he := q.exponent_pos
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      have hr : 2 ≤ r ∧ ¬ (r = 2 ∧ q.card = 2) := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      by_cases hp : q.p = 2
      · iterate 3 right
        left
        show q.p = 2 ∧ 4 ≤ r
        simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
      · iterate 4 right
        left
        show q.p ≠ 2 ∧ 3 ≤ r
        simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
    | C r q =>
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      have hr : 3 ≤ r ∧ q.p ≠ 2 := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      iterate 2 right
      left
      show 4 ≤ r
      omega
    | D r q =>
      have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      iterate 5 right
      left
      show 4 ≤ r
      exact hr
    | twistedD r q =>
      have hr : 4 ≤ r := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      iterate 6 right
      left
      show (q.p ≠ 2 ∧ 4 ≤ r) ∨ (q.p = 2 ∧ 5 ≤ r)
      by_cases hp : q.p = 2
      · simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
      · simp [hp, -PrimePower.card_def] at hlisted hhard hlow ⊢
        omega
    | E6 q =>
      by_cases hp : q.p = 2
      · iterate 8 right
        left
        exact hp
      · iterate 7 right
        left
        exact hp
    | E7 q =>
      by_cases hp : q.p = 2
      · iterate 8 right
        left
        exact hp
      · iterate 7 right
        left
        exact hp
    | E8 q =>
      by_cases hp : q.p = 2
      · iterate 8 right
        left
        exact hp
      · iterate 7 right
        left
        exact hp
    | F4 q =>
      by_cases hp : q.p = 2
      · iterate 10 right
        left
        exact hp
      · iterate 9 right
        left
        exact hp
    | G2 q =>
      have he := q.exponent_pos
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      exfalso
      omega
    | twistedE6 q =>
      by_cases hp : q.p = 2
      · iterate 12 right
        exact hp
      · iterate 11 right
        left
        exact hp
    | trialityD4 q =>
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      exfalso
      omega
    | suzuki m => exact absurd (show N143.IsListedLieIndex (.lie ⟨.suzuki m, hv⟩) from trivial) hlisted
    | reeG2 m =>
      have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 hv'.1
      dsimp only [N143.IsListedLieIndex, N143.IsHardLowTwoIndex, N143.IsHardL3Index,
        N143.IsHardRankTwoIndex, N143.IsHardExceptionalIndex, N143.IsLieLowTwoRankIndex] at hlisted hhard hlow
      exfalso
      omega
    | reeF4 m => exact absurd (show N143.IsListedLieIndex (.lie ⟨.reeF4 m, hv⟩) from trivial) hlisted
    | tits => exact absurd (show N143.IsListedLieIndex (.lie ⟨.tits, hv⟩) from trivial) hlisted

end CFSG.RankThree.PartOne.SLB4A
