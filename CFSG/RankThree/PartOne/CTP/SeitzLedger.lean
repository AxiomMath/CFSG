module

public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzLinearOuter
public import CFSG.RankThree.PartOne.CTP.SeitzL2Odd
public import CFSG.RankThree.PartOne.CTP.SeitzL2Even
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.CTP.SeitzOrthIndex
public import CFSG.RankThree.PartOne.CTP.SeitzD4Index
public import CFSG.RankThree.PartOne.CTP.SeitzUIndex
public import CFSG.RankThree.PartOne.CTP.SeitzUOuter
public import CFSG.RankThree.PartOne.CTP.SeitzExc

public section

namespace CFSG.RankThree.PartOne.CTP

@[expose] def SeitzInnerProved (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ (m : ℕ) (q : TauCeti.PrimePower), d = .A m q ∧ (m ≤ 3 ∨ q.card = 2)) ∨
    (∃ q : TauCeti.PrimePower, d = .B 2 q) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r ∧ q.p = 2) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedD 4 q ∧ q.p = 2) ∨
    (∃ q : TauCeti.PrimePower, d = .D 4 q ∧ q.p = 2 ∧ q.exponent = 1) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 2 q) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 3 q) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 4 q ∧ ¬ 5 ∣ q.p ^ q.exponent + 1) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 5 q ∧ q.p = 2 ∧ q.exponent = 1) ∨
    d = .tits ∨ d = .reeG2 1 ∨ ∃ m : ℕ, d = .suzuki m

@[expose] def SeitzOuterProved (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .A 1 q) ∨
    (∃ (m : ℕ) (q : TauCeti.PrimePower), d = .A m q ∧ 2 ≤ m ∧ (m ≤ 3 ∨ q.card = 2) ∧
      q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .B 2 q ∧ q.exponent < 5) ∨
    (∃ (r : ℕ) (q : TauCeti.PrimePower), d = .B r q ∧ 3 ≤ r ∧ q.p = 2 ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedD 4 q ∧ q.p = 2 ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .D 4 q ∧ q.p = 2 ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 3 q ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 4 q ∧ ¬ 5 ∣ q.p ^ q.exponent + 1 ∧ q.exponent < 5) ∨
    (∃ q : TauCeti.PrimePower, d = .twistedA 5 q ∧ q.p = 2 ∧ q.exponent = 1) ∨
    d = .tits ∨ d = .reeG2 1 ∨ ∃ m : ℕ, d = .suzuki m ∧ 2 * m + 1 < 5

@[expose] def SeitzUnitaryFive (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d = .twistedA 4 q ∧ 5 ∣ q.p ^ q.exponent + 1

@[expose] def SeitzExceptional (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d = .G2 q) ∨ (∃ q : TauCeti.PrimePower, d = .trialityD4 q) ∨
    (∃ m : ℕ, d = .reeF4 m) ∨ ∃ q : TauCeti.PrimePower, d = .F4 q

@[expose] def SeitzSmallExponent (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, (d = .G2 q ∨ d = .trialityD4 q ∨ d = .F4 q) ∧ q.exponent < 5) ∨
    ∃ m : ℕ, d = .reeF4 m ∧ 2 * m + 1 < 5

theorem SeitzSmallExponent.exceptional {d : TauCeti.LieTypeIndex} (h : SeitzSmallExponent d) :
    SeitzExceptional d := by
  rcases h with ⟨q, hq | hq | hq, -⟩ | ⟨m, hm, -⟩
  · exact Or.inl ⟨q, hq⟩
  · exact Or.inr (Or.inl ⟨q, hq⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨q, hq⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨m, hm⟩))

theorem seitzInnerProved_or_five_or_exceptional {d : TauCeti.LieTypeIndex}
    (hd : Thm3LieIndex d) :
    SeitzInnerProved d ∨ SeitzUnitaryFive d ∨ SeitzExceptional d := by
  unfold SeitzInnerProved SeitzUnitaryFive SeitzExceptional
  rcases hd with ⟨q, -, -, rfl⟩ | ⟨q, -, -, rfl | rfl⟩ | rfl | ⟨q, -, -, rfl | rfl | rfl | rfl⟩ |
    ⟨q, -, rfl⟩ | ⟨m, rfl⟩ | ⟨q, -, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ | ⟨m, rfl⟩ | rfl |
    ⟨q, hq2, rfl | rfl | rfl⟩ | ⟨q, hq2, he, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩
  · left; left; exact ⟨1, q, rfl, Or.inl (by norm_num)⟩
  · left; left; exact ⟨2, q, rfl, Or.inl (by norm_num)⟩
  · left; (iterate 5 right); left; exact ⟨q, rfl⟩
  · left; (iterate 10 right); left; exact rfl
  · right; right; left; exact ⟨q, rfl⟩
  · left; (iterate 1 right); left; exact ⟨q, rfl⟩
  · left; (iterate 6 right); left; exact ⟨q, rfl⟩
  · left; left; exact ⟨3, q, rfl, Or.inl (by norm_num)⟩
  · left; left; exact ⟨1, q, rfl, Or.inl (by norm_num)⟩
  · left; (iterate 11 right); exact ⟨m, rfl⟩
  · left; (iterate 5 right); left; exact ⟨q, rfl⟩
  · left; left; exact ⟨2, q, rfl, Or.inl (by norm_num)⟩
  · left; (iterate 1 right); left; exact ⟨q, rfl⟩
  · right; right; left; exact ⟨q, rfl⟩
  · left; (iterate 6 right); left; exact ⟨q, rfl⟩
  · by_cases h5 : 5 ∣ q.p ^ q.exponent + 1
    · right; left; exact ⟨q, rfl, h5⟩
    · left; (iterate 7 right); left; exact ⟨q, rfl, h5⟩
  · right; right; (iterate 1 right); left; exact ⟨q, rfl⟩
  · right; right; (iterate 2 right); left; exact ⟨m, rfl⟩
  · left; (iterate 9 right); left; exact rfl
  · left; left; exact ⟨3, q, rfl, Or.inl (by norm_num)⟩
  · left; (iterate 2 right); left; exact ⟨3, q, rfl, le_rfl, hq2⟩
  · left; (iterate 3 right); left; exact ⟨q, rfl, hq2⟩
  · left; left; exact ⟨4, q, rfl, Or.inr (by simp [TauCeti.PrimePower.card_def, hq2, he])⟩
  · left; left; exact ⟨5, q, rfl, Or.inr (by simp [TauCeti.PrimePower.card_def, hq2, he])⟩
  · left; left; exact ⟨6, q, rfl, Or.inr (by simp [TauCeti.PrimePower.card_def, hq2, he])⟩
  · left; (iterate 8 right); left; exact ⟨q, rfl, hq2, he⟩
  · left; (iterate 2 right); left; exact ⟨4, q, rfl, by norm_num, hq2⟩
  · left; (iterate 4 right); left; exact ⟨q, rfl, hq2, he⟩
  · right; right; (iterate 3 right); exact ⟨q, rfl⟩

@[expose] def SeitzFieldAutGeneration : Prop :=
  ∀ d : TauCeti.LieTypeIndex, Thm3LieIndex d → ¬ SeitzOuterProved d → ¬ SeitzUnitaryFive d →
    ¬ SeitzSmallExponent d → ExtSeitzAtOuter d

@[expose] def SeitzUnitaryFiveGeneration : Prop :=
  ∀ d : TauCeti.LieTypeIndex, Thm3LieIndex d → SeitzUnitaryFive d → ExtSeitzAt d

@[expose] def SeitzExceptionalGeneration : Prop :=
  ∀ d : TauCeti.LieTypeIndex, Thm3LieIndex d → SeitzExceptional d →
    ExtSeitzAtInner d ∧ (SeitzSmallExponent d → ExtSeitzAtOuter d)

@[expose] def SeitzResidual : Prop :=
  SeitzFieldAutGeneration ∧ SeitzUnitaryFiveGeneration ∧ SeitzExceptionalGeneration

theorem extSeitzThree_of_residual
    (h : SeitzResidual) :
    ExtSeitzThree := by
  intro d hd
  by_cases hu : SeitzUnitaryFive d
  · exact h.2.1 d hd hu
  refine extSeitzAt_of_inner_outer ?_ ?_
  · by_cases hi : SeitzInnerProved d
    · rcases hi with ⟨m, q, rfl, hmq⟩ | ⟨q, rfl⟩ | ⟨r, q, rfl, hr, hq⟩ | ⟨q, rfl, hq⟩ |
        ⟨q, rfl, hq, he⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq, he⟩ | rfl | rfl |
        ⟨m, rfl⟩
      · exact extSeitzAtInner_A hmq
      · exact extSeitzAtInner_B2 q
      · exact extSeitzAtInner_B_even hr hq
      · exact extSeitzAtInner_twistedD_four hq
      · exact D4Two.extSeitzAtInner_D_four_two hq he
      · exact extSeitzAtInner_twistedA_two q
      · exact extSeitzAtInner_twistedA_three q
      · exact extSeitzAtInner_twistedA_four_of_not_dvd hq
      · exact extSeitzAtInner_twistedA_five hq he
      · exact extSeitzAtInner_of_extSeitzAt extSeitzAt_tits
      · exact extSeitzAtInner_of_extSeitzAt extSeitzAt_reeG2_one
      · exact extSeitzAtInner_suzuki m
    · rcases seitzInnerProved_or_five_or_exceptional hd with hi' | hu' | hx
      · exact absurd hi' hi
      · exact absurd hu' hu
      · exact (h.2.2 d hd hx).1
  · by_cases ho : SeitzOuterProved d
    · rcases ho with ⟨q, rfl⟩ | ⟨m, q, rfl, hm2, hmq, he⟩ | ⟨q, rfl, he⟩ |
        ⟨r, q, rfl, hr, hq, he⟩ | ⟨q, rfl, hq, he⟩ | ⟨q, rfl, hq, he⟩ | ⟨q, rfl, he⟩ |
        ⟨q, rfl, he⟩ | ⟨q, rfl, h5, he⟩ | ⟨q, rfl, hq, he⟩ | rfl | rfl | ⟨m, rfl, hm⟩
      · by_cases h2 : q.p = 2
        · exact extSeitzAtOuter_A1_even h2
        · exact extSeitzAtOuter_A1_odd h2
      · exact extSeitzAtOuter_A_of_exponent_lt_five hm2 hmq he
      · exact extSeitzAtOuter_B2_of_exponent_lt_five he
      · exact extSeitzAtOuter_B_even_of_exponent_lt_five hr hq he
      · exact extSeitzAtOuter_twistedD_four_of_exponent_lt_five hq he
      · exact extSeitzAtOuter_D_four_of_exponent_lt_five hq he
      · exact extSeitzAtOuter_twistedA_two he
      · exact extSeitzAtOuter_twistedA_three he
      · exact extSeitzAtOuter_twistedA_four he h5
      · exact extSeitzAtOuter_twistedA_five hq he
      · exact extSeitzAtOuter_of_extSeitzAt extSeitzAt_tits
      · exact extSeitzAtOuter_of_extSeitzAt extSeitzAt_reeG2_one
      · exact extSeitzAtOuter_suzuki_of_lt_five hm
    · by_cases hs : SeitzSmallExponent d
      · exact (h.2.2 d hd hs.exceptional).2 hs
      · exact h.1 d hd ho hu hs

end CFSG.RankThree.PartOne.CTP
