module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K9Rows : Prop where
  one : ∀ (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e → RowOfK9 (projSL 2 (GaloisField p e))
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOfK9 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOfK9 (projSU 3 p e)
  three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOfK9 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfK9 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfK9 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOfK9 (projSU 4 p 1)
  five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOfK9 (alternatingGroup (Fin n))
  six : ∀ s ∈ sporadics42, RowOfK9 (Spor s)
  seven_SL2 : ∀ n : ℕ, 1 ≤ n → RowOfK9 (projSL 2 (GaloisField 2 n))
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowOfK9 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowOfK9 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOfK9 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOfK9 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_Sz : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid),
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOfK9 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SL5 : RowOfK9 (projSL 5 (GaloisField 2 1))
  eight_SU5 : RowOfK9 (projSU 5 2 1)
  eight_SL6 : RowOfK9 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowOfK9 (projSU 6 2 1)
  eight_SL7 : RowOfK9 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowOfK9 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowOfK9 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowOfK9 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOfK9 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowOfK9 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowOfK9 (projSp 3 (GaloisField 2 2))
  eight_SU5_4 : RowOfK9 (projSU 5 2 2)
  eight_SU5_8 : RowOfK9 (projSU 5 2 3)
  eight_F4 : RowOfK9 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOfK9 (projSL 3 (GaloisField 3 e))
  nine_SU3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOfK9 (projSU 3 3 e)
  nine_G2 : RowOfK9 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group
  nine_SL4 : RowOfK9 (projSL 4 (GaloisField 3 1))
  nine_SU4 : RowOfK9 (projSU 4 3 1)

theorem K9Rows.row_of_list42 (R : K9Rows) {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : Sec4.Census.List42 S) : NoCfgJ2 S := by
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

theorem res3K9_of_rows (h42 : Sec4.Item4_2) (R : K9Rows) : Res3K9 := by
  intro S _ _ hS hs hna σ h3 h1 C P hC hPC hsn hP N _
  obtain rfl : C = Sec4.autFix σ := Subgroup.ext fun x => (hC x).trans Sec4.mem_autFix.symm
  exact R.row_of_list42 hs hna (Sec4.Census.item4_2_iff.mp h42 S hS hs hna) σ h3 h1 P hPC hsn hP N

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
