module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTransfer
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Census
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def RowSOf429 (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → RowS429 S

theorem rowSOf429_of_noCfg {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → NoCfgS429 S) : RowSOf429 X :=
  fun S _ _ hs hna hX => (h S hs hna hX).rowS429

theorem rowSOf429_of_noL3 {X : Type} [Group X]
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* X) → RowS429NoL3 S) : RowSOf429 X :=
  fun S _ _ hs hna hX => (h S hs hna hX).rowS429

structure K429RowsS : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowSOf429 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSOf429 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowSOf429 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowSOf429 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf429 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf429 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowSOf429 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowSOf429 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowSOf429 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf429 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowSOf429 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowSOf429 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowSOf429 (projSU 5 2 1)
  eight_SL6 : RowSOf429 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowSOf429 (projSU 6 2 1)
  eight_SL7 : RowSOf429 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowSOf429 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowSOf429 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf429 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf429 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf429 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf429 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowSOf429 (projSU 5 2 2)
  eight_SU5_8 : RowSOf429 (projSU 5 2 3)
  eight_F4 : RowSOf429 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf429 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowSOf429 (projSU 3 3 e)
  nine_G2 : RowSOf429 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowSOf429 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowSOf429 (projSU 4 3 1)

namespace K429RowsS

variable {S : Type} [Group S] [Finite S]

theorem rowS_of_list42 (R : K429RowsS) (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Census.List42 S) : RowS429 S := by
  rcases h with ⟨p, e, hp, h2, he, hf⟩ | ⟨p, e, hp, h3, he, he2, hf | hf⟩ | ⟨hr, hf⟩ |
    ⟨p, hp, h3, ⟨q, hqp, hqe, hq, hf⟩ | hf | hf | hf⟩ | ⟨n, hn5, hn12, hf⟩ |
    ⟨s, hsp, hf⟩ | h7 | h8 | h9
  · exact R.one p e h2 he S hs hna hf
  · exact R.two_SL p e h3 he he2 S hs hna hf
  · exact R.two_SU p e h3 he he2 S hs hna hf
  · exact R.three hr S hs hna hf
  · exact R.four_G2 p h3 q hqp hqe hq S hs hna hf
  · exact R.four_Sp p h3 S hs hna hf
  · exact R.four_SL p h3 S hs hna hf
  · exact R.four_SU p h3 S hs hna hf
  · exact R.five n hn5 hn12 S hs hna hf
  · exact R.six s hsp S hs hna hf
  · rcases h7 with ⟨n, hn, hf | hf | hf | hf | hf⟩ | ⟨q, hq2, hq, hf⟩ |
      ⟨q, hq, hq2, hf⟩ | ⟨m, hm, hf⟩ | ⟨m, hm, hf⟩ | ⟨ht, hf⟩
    · exact R.seven_SL2 n hn S hs hna hf
    · exact R.seven_SL3 n hn S hs hna hf
    · exact R.seven_SU3 n hn S hs hna hf
    · exact R.seven_Sp4 n hn S hs hna hf
    · exact R.seven_SU4 n hn S hs hna hf
    · exact R.seven_G2 q hq2 hq S hs hna hf
    · exact R.seven_D4 q hq hq2 S hs hna hf
    · exact R.seven_Sz m hm S hs hna hf
    · exact R.seven_F4 m hm S hs hna hf
    · exact R.seven_Tits ht S hs hna hf
  · rcases h8 with hf | hf | hf | hf | hf | hf | hf | hf | ⟨b, c, hbc, hf⟩ | hf |
      hf | hf | hf | hf
    · exact R.eight_SL5 S hs hna hf
    · exact R.eight_SU5 S hs hna hf
    · exact R.eight_SL6 S hs hna hf
    · exact R.eight_SU6 S hs hna hf
    · exact R.eight_SL7 S hs hna hf
    · exact R.eight_Sp6 S hs hna hf
    · exact R.eight_Sp8 S hs hna hf
    · exact R.eight_OmegaPlus S hs hna hf
    · exact R.eight_OmegaMinus b c hbc S hs hna hf
    · exact R.eight_SL4 S hs hna hf
    · exact R.eight_Sp6_4 S hs hna hf
    · exact R.eight_SU5_4 S hs hna hf
    · exact R.eight_SU5_8 S hs hna hf
    · exact R.eight_F4 S hs hna hf
  · rcases h9 with ⟨e, he, he3, hf | hf⟩ | hf | hf | hf
    · exact R.nine_SL3 e he he3 S hs hna hf
    · exact R.nine_SU3 e he he3 S hs hna hf
    · exact R.nine_G2 S hs hna hf
    · exact R.nine_SL4 S hs hna hf
    · exact R.nine_SU4 S hs hna hf

end K429RowsS

section Transfer

theorem K429RowsS.toK429Rows (R : K429RowsS) (h45 : Item4_5) (hcov : K429CoverL3) :
    K429Rows where
  one p e _ h2 he := rowOf429_of_rowS h45 hcov (R.one p e h2 he)
  two_SL p e _ h3 he he2 := rowOf429_of_rowS h45 hcov (R.two_SL p e h3 he he2)
  two_SU p e _ h3 he he2 := rowOf429_of_rowS h45 hcov (R.two_SU p e h3 he he2)
  three hr := rowOf429_of_rowS h45 hcov (R.three hr)
  four_G2 p _ h3 q hqp hqe hq := rowOf429_of_rowS h45 hcov (R.four_G2 p h3 q hqp hqe hq)
  four_Sp p _ h3 := rowOf429_of_rowS h45 hcov (R.four_Sp p h3)
  four_SL p _ h3 := rowOf429_of_rowS h45 hcov (R.four_SL p h3)
  four_SU p _ h3 := rowOf429_of_rowS h45 hcov (R.four_SU p h3)
  five n h5 h12 := rowOf429_of_rowS h45 hcov (R.five n h5 h12)
  six s hs := rowOf429_of_rowS h45 hcov (R.six s hs)
  seven_SL2 n hn := rowOf429_of_rowS h45 hcov (R.seven_SL2 n hn)
  seven_SL3 n hn := rowOf429_of_rowS h45 hcov (R.seven_SL3 n hn)
  seven_SU3 n hn := rowOf429_of_rowS h45 hcov (R.seven_SU3 n hn)
  seven_Sp4 n hn := rowOf429_of_rowS h45 hcov (R.seven_Sp4 n hn)
  seven_SU4 n hn := rowOf429_of_rowS h45 hcov (R.seven_SU4 n hn)
  seven_G2 q hq2 hq := rowOf429_of_rowS h45 hcov (R.seven_G2 q hq2 hq)
  seven_D4 q hq hq2 := rowOf429_of_rowS h45 hcov (R.seven_D4 q hq hq2)
  seven_Sz m hm := rowOf429_of_rowS h45 hcov (R.seven_Sz m hm)
  seven_F4 m hm := rowOf429_of_rowS h45 hcov (R.seven_F4 m hm)
  seven_Tits ht := rowOf429_of_rowS h45 hcov (R.seven_Tits ht)
  eight_SL5 := rowOf429_of_rowS h45 hcov R.eight_SL5
  eight_SU5 := rowOf429_of_rowS h45 hcov R.eight_SU5
  eight_SL6 := rowOf429_of_rowS h45 hcov R.eight_SL6
  eight_SU6 := rowOf429_of_rowS h45 hcov R.eight_SU6
  eight_SL7 := rowOf429_of_rowS h45 hcov R.eight_SL7
  eight_Sp6 := rowOf429_of_rowS h45 hcov R.eight_Sp6
  eight_Sp8 := rowOf429_of_rowS h45 hcov R.eight_Sp8
  eight_OmegaPlus := rowOf429_of_rowS h45 hcov R.eight_OmegaPlus
  eight_OmegaMinus b c hbc := rowOf429_of_rowS h45 hcov (R.eight_OmegaMinus b c hbc)
  eight_SL4 := rowOf429_of_rowS h45 hcov R.eight_SL4
  eight_Sp6_4 := rowOf429_of_rowS h45 hcov R.eight_Sp6_4
  eight_SU5_4 := rowOf429_of_rowS h45 hcov R.eight_SU5_4
  eight_SU5_8 := rowOf429_of_rowS h45 hcov R.eight_SU5_8
  eight_F4 := rowOf429_of_rowS h45 hcov R.eight_F4
  nine_SL3 e he he3 := rowOf429_of_rowS h45 hcov (R.nine_SL3 e he he3)
  nine_SU3 e he he3 := rowOf429_of_rowS h45 hcov (R.nine_SU3 e he he3)
  nine_G2 := rowOf429_of_rowS h45 hcov R.nine_G2
  nine_SL4 := rowOf429_of_rowS h45 hcov R.nine_SL4
  nine_SU4 := rowOf429_of_rowS h45 hcov R.nine_SU4

end Transfer

section Census

theorem item4_29Outer_of_rowsS
    (R : K429RowsS) (h45 : Item4_5) (hcov : K429CoverL3) :
    Item4_29Outer :=
  item4_29Outer_of_rows (R.toK429Rows h45 hcov)

theorem item4_29_of_rowsS
    (R : K429RowsS) (hcov : K429CoverL3) : Item4_29 :=
  item4_29_of rank3II_4_5 (item4_29Outer_of_rowsS R rank3II_4_5 hcov)

end Census

end CFSG.RankThree.PartTwo.Sec4.RonanK429
