module

public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.SeitzFineD4
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLPair
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSp
public import CFSG.RankThree.PartOne.CTP.SeitzMaxUnitary
public import CFSG.RankThree.PartOne.CTP.SeitzU5Heis
public import CFSG.RankThree.PartOne.SEITZX.F4Two
public import CFSG.RankThree.PartOne.SEITZX.ReeSplit

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def FieldAutOmega8m : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.twistedD 4 q)

@[expose] def FieldAutG2 : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.G2 q)

@[expose] def FieldAut3D4 : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.trialityD4 q)

@[expose] def FieldAutSz : Prop :=
  ∀ m : ℕ, 2 ≤ m → ExtSeitzAtOuter (.suzuki m)

@[expose] def FieldAut2F4 : Prop :=
  ∀ m : ℕ, 2 ≤ m → ExtSeitzAtOuter (.reeF4 m)

theorem fieldAutA2_of_pair (h : SubfieldPairSL 3) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.A 2 q) :=
  
  fun _ hq _ => extSeitzAtOuter_A_of_pair (m := 2) (by norm_num) (by norm_num) h hq

theorem fieldAutA3_of_pair (h : SubfieldPairSL 4) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.A 3 q) :=
  
  fun _ hq _ => extSeitzAtOuter_A_of_pair (m := 3) (by norm_num) (by norm_num) h hq

theorem fieldAutU3_of_pair (h : SubfieldPairSU 3) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.twistedA 2 q) :=
  
  fun _ hq _ => extSeitzAtOuter_twistedA_small_of_pair (m := 2) (by norm_num) (by norm_num) h hq

theorem fieldAutU4_of_pair (h : SubfieldPairSU 4) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.twistedA 3 q) :=
  
  fun _ hq _ => extSeitzAtOuter_twistedA_small_of_pair (m := 3) (by norm_num) (by norm_num) h hq

theorem fieldAutU5_of_pair (h : SubfieldPairSU 5) :
    ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ¬ 5 ∣ q.p ^ q.exponent + 1 →
      ExtSeitzAtOuter (.twistedA 4 q) :=
  fun _ hq _ h5 => extSeitzAtOuter_twistedA_four_of_pair h hq h5

theorem fieldAutB2_of_pair (h : SubfieldPairSp 2) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.B 2 q) :=
  
  fun _ hq _ => extSeitzAtOuter_B_of_pair (r := 2) (by norm_num) (by norm_num) h hq

theorem fieldAutB3_of_pair (h : SubfieldPairSp 3) : ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → ExtSeitzAtOuter (.B 3 q) :=
  
  fun _ hq _ => extSeitzAtOuter_B_of_pair (r := 3) (by norm_num) (by norm_num) h hq

@[expose] def SeitzFieldAutFine : Prop :=
  SubfieldPairSU 3 ∧ SubfieldPairSU 4 ∧ SubfieldPairSU 5 ∧
    SubfieldPairSp 2 ∧ SubfieldPairSp 3 ∧ FieldAutOmega8m ∧ FieldAutG2 ∧ FieldAut3D4 ∧
    FieldAutSz ∧ FieldAut2F4

theorem seitzFieldAut_of_fine (h : SeitzFieldAutFine) :
    SeitzFieldAutGeneration := by
  obtain ⟨hSU3, hSU4, hSU5, hSp2, hSp3, hOm, hG2, h3D4, hSz, h2F4⟩ := h
  have hA2 := fieldAutA2_of_pair (subfieldPairSL (by norm_num) (by norm_num))
  have hA3 := fieldAutA3_of_pair (subfieldPairSL (by norm_num) (by norm_num))
  have hU3 := fieldAutU3_of_pair hSU3
  have hU4 := fieldAutU4_of_pair hSU4
  have hU5 := fieldAutU5_of_pair hSU5
  have hB2 := fieldAutB2_of_pair hSp2
  have hB3 := fieldAutB3_of_pair hSp3
  intro d hd hnO hnU hnS
  rcases thm3_outer_cases hd with h1 | h1 | h1 | ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, rfl⟩ |
    ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, h5, rfl⟩ | ⟨q, hq, he, rfl⟩ |
    ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, rfl⟩ | ⟨q, hq, he, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, hm, rfl⟩
  · exact absurd h1 hnO
  · exact absurd h1 hnU
  · exact absurd h1 hnS
  · exact hA2 q hq he
  · exact hA3 q hq he
  · exact hU3 q hq he
  · exact hU4 q hq he
  · exact hU5 q hq he h5
  · exact hB2 q hq he
  · exact hB3 q hq he
  · exact hOm q hq he
  · exact hG2 q hq he
  · exact h3D4 q hq he
  · exact hSz m hm
  · exact h2F4 m hm

theorem thm3_twistedA4 {q : TauCeti.PrimePower} (hd : Thm3LieIndex (.twistedA 4 q)) : q.p = 2 := by
  rcases hd with ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h | ⟨q', -, -, h | h | h | h⟩ |
    ⟨q', -, h⟩ | ⟨m, h⟩ | ⟨q', hq2, h | h | h | h | h | h | h⟩ | ⟨m, h⟩ | h |
    ⟨q', hq2, h | h | h⟩ | ⟨q', hq2, he, h | h | h | h | h | h | h⟩
  all_goals first
    | (exfalso; cases h; done)
    | (injection h with h1 h2; subst h2; assumption)

theorem u5FieldAut_of_pair (h : SubfieldPairSU 5) :
    ∀ q : TauCeti.PrimePower, q.p = 2 → 5 ≤ q.exponent → 5 ∣ q.p ^ q.exponent + 1 →
      ExtSeitzAtOuterFor (.twistedA 4 q) fun p => p ≠ 5 :=
  fun _ hq _ _ => extSeitzAtOuterFor_twistedA_four_ne_five_of_pair h hq

@[expose] def SeitzUnitaryFiveFine : Prop :=
  PSU5DiagPlane49 ∧ PSU5FieldPlane

theorem seitzUnitaryFive_of_fine (hU5 : SubfieldPairSU 5) (h : SeitzUnitaryFiveFine) :
    SeitzUnitaryFiveGeneration := by
  obtain ⟨h49, hP5⟩ := h
  have hD5 := psu5DiagNonabelianPlane_of_parts psu5DiagPlane48 h49
  have hF := u5FieldAut_of_pair hU5
  intro d hd hu
  obtain ⟨q, rfl, h5⟩ := hu
  have hq2 : q.p = 2 := thm3_twistedA4 hd
  refine extSeitzAt_of_inner_outer ?_ ?_
  · exact extSeitzAtInner_of_split (fun p => p = 5)
      (extSeitzAtInnerFor_twistedA_four_five hD5 hq2 h5)
      (extSeitzAtInnerFor_twistedA_four_ne_five.mono fun p hp => hp)
  · refine extSeitzAtOuter_of_split (fun p => p = 5)
      (extSeitzAtOuterFor_twistedA_four_five hD5 hP5 hq2 h5) ?_
    by_cases he : q.exponent < 5
    · exact (extSeitzAtOuterFor_twistedA_four_ne_five he).mono fun p hp => hp
    · exact (hF q hq2 (by omega) h5).mono fun p hp => hp

theorem thm3_G2 {q : TauCeti.PrimePower} (hd : Thm3LieIndex (.G2 q)) :
    q.p = 2 ∨ (q.p ≠ 2 ∧ q.exponent = 1) := by
  rcases hd with ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h | ⟨q', hq, he, h | h | h | h⟩ |
    ⟨q', -, h⟩ | ⟨m, h⟩ | ⟨q', hq2, h | h | h | h | h | h | h⟩ | ⟨m, h⟩ | h |
    ⟨q', hq2, h | h | h⟩ | ⟨q', hq2, he, h | h | h | h | h | h | h⟩
  all_goals first
    | (exfalso; cases h; done)
    | (injection h with h2; subst h2; first | exact Or.inl hq2 | exact Or.inr ⟨hq, he⟩)

theorem thm3_trialityD4 {q : TauCeti.PrimePower} (hd : Thm3LieIndex (.trialityD4 q)) :
    q.p = 2 := by
  rcases hd with ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h | ⟨q', -, -, h | h | h | h⟩ |
    ⟨q', -, h⟩ | ⟨m, h⟩ | ⟨q', hq2, h | h | h | h | h | h | h⟩ | ⟨m, h⟩ | h |
    ⟨q', hq2, h | h | h⟩ | ⟨q', hq2, he, h | h | h | h | h | h | h⟩
  all_goals first
    | (exfalso; cases h; done)
    | (injection h with h2; subst h2; assumption)

theorem thm3_F4 {q : TauCeti.PrimePower} (hd : Thm3LieIndex (.F4 q)) :
    q.p = 2 ∧ q.exponent = 1 := by
  rcases hd with ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h | ⟨q', -, -, h | h | h | h⟩ |
    ⟨q', -, h⟩ | ⟨m, h⟩ | ⟨q', hq2, h | h | h | h | h | h | h⟩ | ⟨m, h⟩ | h |
    ⟨q', hq2, h | h | h⟩ | ⟨q', hq2, he, h | h | h | h | h | h | h⟩
  all_goals first
    | (exfalso; cases h; done)
    | (injection h with h2; subst h2; exact ⟨hq2, he⟩)

theorem SeitzSmallExponent.of_G2 {q : TauCeti.PrimePower} (h : SeitzSmallExponent (.G2 q)) :
    q.exponent < 5 := by
  rcases h with ⟨q', h1 | h1 | h1, he⟩ | ⟨m, h1, -⟩
  all_goals first
    | (exfalso; cases h1; done)
    | (injection h1 with h2; subst h2; exact he)

theorem SeitzSmallExponent.of_trialityD4 {q : TauCeti.PrimePower}
    (h : SeitzSmallExponent (.trialityD4 q)) : q.exponent < 5 := by
  rcases h with ⟨q', h1 | h1 | h1, he⟩ | ⟨m, h1, -⟩
  all_goals first
    | (exfalso; cases h1; done)
    | (injection h1 with h2; subst h2; exact he)

theorem SeitzSmallExponent.of_reeF4 {m : ℕ} (h : SeitzSmallExponent (.reeF4 m)) :
    2 * m + 1 < 5 := by
  rcases h with ⟨q', h1 | h1 | h1, he⟩ | ⟨m', h1, hm⟩
  all_goals first
    | (exfalso; cases h1; done)
    | (injection h1 with h2; subst h2; exact hm)

@[expose] def GoodG2 (q : TauCeti.PrimePower) : Prop :=
  q.p = 2 ∨ (q.exponent = 1 ∧ 11 ≤ q.card)

@[expose] def ExcG2Nonsplit : Prop :=
  ∀ q : TauCeti.PrimePower, GoodG2 q → ExtSeitzAtInnerFor (.G2 q) fun p => ¬ p ∣ q.card - 1

@[expose] def Exc3D4Nonsplit : Prop :=
  ∀ q : TauCeti.PrimePower, q.p = 2 →
    ExtSeitzAtInnerFor (.trialityD4 q) fun p => ¬ p ∣ q.card - 1

@[expose] def Exc2F4Nonsplit : Prop :=
  ∀ m : ℕ, ExtSeitzAtInnerFor (.reeF4 m) fun p => ¬ p ∣ 2 ^ (2 * m + 1) - 1

@[expose] def SeitzExceptionalFine : Prop :=
  ExcG2Nonsplit ∧ Exc3D4Nonsplit ∧ Exc2F4Nonsplit

theorem seitzExceptional_of_fine
    (h : SeitzExceptionalFine) : SeitzExceptionalGeneration := by
  obtain ⟨hG2n, h3n, h2n⟩ := h
  intro d hd hx
  rcases hx with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩ | ⟨q, rfl⟩
  · refine ⟨?_, fun hs => ?_⟩
    · by_cases hg : GoodG2 q
      · exact extSeitzAtInner_of_split _ extSeitzAtInnerFor_G2_split (hG2n q hg)
      · rcases thm3_G2 hd with h2 | ⟨h2, h1⟩
        · exact absurd (Or.inl h2) hg
        · exact extSeitzAtInner_G2_odd_small h2 h1 (by
            by_contra h11
            exact hg (Or.inr ⟨h1, by omega⟩))
    · rcases thm3_G2 hd with h2 | ⟨h2, h1⟩
      · exact extSeitzAtOuter_G2_even_of_lt_five h2 hs.of_G2
      · exact extSeitzAtOuter_G2_odd h2 h1
  · exact ⟨extSeitzAtInner_of_split _ (extSeitzAtInnerFor_trialityD4_split (thm3_trialityD4 hd))
      (h3n q (thm3_trialityD4 hd)),
      fun hs => extSeitzAtOuter_trialityD4_of_lt_five (thm3_trialityD4 hd) hs.of_trialityD4⟩
  · exact ⟨extSeitzAtInner_of_split _ (SEITZX.extSeitzAtInnerFor_reeF4_split m) (h2n m),
      fun hs => extSeitzAtOuter_reeF4_of_lt_five hs.of_reeF4⟩
  · exact ⟨SEITZX.extSeitzAtInner_F4_two q (thm3_F4 hd).1 (thm3_F4 hd).2,
      fun _ => extSeitzAtOuter_F4_two (thm3_F4 hd).1 (thm3_F4 hd).2⟩

theorem seitzResidual_of_fine
    (h : SeitzFieldAutFine ∧ SeitzUnitaryFiveFine ∧ SeitzExceptionalFine) : SeitzResidual :=
  ⟨seitzFieldAut_of_fine h.1, seitzUnitaryFive_of_fine h.1.2.2.1 h.2.1,
    seitzExceptional_of_fine h.2.2⟩

end CFSG.RankThree.PartOne.CTP
