module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowsEasy
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowL2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowON
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowJ2
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowCo
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowSuzLy
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowHNTh
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowJ3McL
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowAltLarge
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM12

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

theorem noCQOf_on :
    NoCQOf (Spor .ONan) :=
  fun _ _ _ _ _ ⟨e⟩ => noCC425_of_abelian_sylow (sylow_three_comm_of_ON e)

@[expose] def sporadicsOpen425 : List TauCeti.SporadicName :=
  [.He]

structure K425OpenRows : Prop where
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowOf425 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf425 (projSU 3 p e)
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSU 4 p 1)
  six_open : ∀ s ∈ sporadicsOpen425, RowOf425 (Spor s)
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSU 3 2 n)
  seven_Sp4 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf425 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  seven_Tits : ∀ ht : TauCeti.LieTypeIndex.tits.Valid,
    RowOf425 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group
  eight_SU5 : RowOf425 (projSU 5 2 1)
  eight_SL6 : RowOf425 (projSL 6 (GaloisField 2 1))
  eight_SU6 : RowOf425 (projSU 6 2 1)
  eight_SL7 : RowOf425 (projSL 7 (GaloisField 2 1))
  eight_Sp6 : RowOf425 (projSp 3 (GaloisField 2 1))
  eight_Sp8 : RowOf425 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowOf425 (projOmegaPlus 4 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowOf425 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowOf425 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowOf425 (projSp 3 (GaloisField 2 2))
  eight_SU5_8 : RowOf425 (projSU 5 2 3)
  eight_F4 : RowOf425 (TauCeti.CFSGIndex.lie f4TwoIndex).Group
  nine_SL3_nine : RowOf425 (projSL 3 (GaloisField 3 2))
  nine_SU3_nine : RowOf425 (projSU 3 3 2)
  nine_SL4 : RowOf425 (projSL 4 (GaloisField 3 1))

section Assembly

theorem six425_of_open
    (O : K425OpenRows) : ∀ s ∈ sporadics42, RowOf425 (Spor s) := by
  intro s hs
  have hopen : ∀ s ∈ sporadicsOpen425, RowOf425 (Spor s) := O.six_open
  simp only [sporadics42, List.mem_cons, List.mem_nil_iff, or_false] at hs
  simp only [sporadicsOpen425, List.mem_cons, List.mem_nil_iff, or_false] at hopen
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowOf425_of_noCQ noCQOf_m11
  · exact rowOf425_m12
  · exact rowOf425_of_noCQ noCQOf_m22
  · exact rowOf425_of_noCQ noCQOf_m23
  · exact rowOf425_m24
  · exact rowOf425_of_noCQ noCQOf_j1
  · exact rowOf425_j2
  · exact rowOf425_j3
  · exact rowOf425_j4
  · exact rowOf425_mcl
  · exact rowOf425_ly
  · exact rowOf425_of_noCQ noCQOf_hs
  · exact hopen _ (by simp)
  · exact rowOf425_suz
  · exact rowOf425_ru
  · exact rowOf425_of_noCQ noCQOf_on
  · exact rowOf425_co3
  · exact rowOf425_co2
  · exact rowOf425_hn
  · exact rowOf425_th

theorem k425Rows_of_open
    (O : K425OpenRows) : K425Rows where
  one p e _ _ _ := rowOf425_of_noCQ (noCQOf_projSL_two _)
  two_SL := O.two_SL
  two_SU := O.two_SU
  three hr := rowOf425_of_noCQ (noCQOf_three hr)
  four_G2 := O.four_G2
  four_Sp := O.four_Sp
  four_SL := O.four_SL
  four_SU := O.four_SU
  five n _ hn12 := rowOf425_of_noCQ (noCQOf_alternating_le_fourteen (by omega))
  six := six425_of_open O
  seven_SL2 n _ := rowOf425_of_noCQ (noCQOf_projSL_two _)
  seven_SL3 := O.seven_SL3
  seven_SU3 := O.seven_SU3
  seven_Sp4 := O.seven_Sp4
  seven_SU4 := O.seven_SU4
  seven_G2 := O.seven_G2
  seven_D4 := O.seven_D4
  seven_Sz m hm := rowOf425_of_noCQ (noCQOf_seven_Sz m hm)
  seven_F4 := O.seven_F4
  seven_Tits := O.seven_Tits
  eight_SL5 := rowOf425_of_noCQ noCQOf_eight_SL5
  eight_SU5 := O.eight_SU5
  eight_SL6 := O.eight_SL6
  eight_SU6 := O.eight_SU6
  eight_SL7 := O.eight_SL7
  eight_Sp6 := O.eight_Sp6
  eight_Sp8 := O.eight_Sp8
  eight_OmegaPlus := O.eight_OmegaPlus
  eight_OmegaMinus := O.eight_OmegaMinus
  eight_SL4 := O.eight_SL4
  eight_Sp6_4 := O.eight_Sp6_4
  eight_SU5_4 := rowOf425_of_noCQ noCQOf_eight_SU5_4
  eight_SU5_8 := O.eight_SU5_8
  eight_F4 := O.eight_F4
  nine_SL3 e he he3 := by
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    · exact rowOf425_of_noCQ (noCQOf_projSL_three_char_three (Or.inl rfl))
    · exact O.nine_SL3_nine
    · exact rowOf425_of_noCQ (noCQOf_projSL_three_char_three (Or.inr rfl))
  nine_SU3 e he he3 := by
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    · exact rowOf425_of_noCQ (noCQOf_projSU_three_char_three (Or.inl rfl))
    · exact O.nine_SU3_nine
    · exact rowOf425_of_noCQ (noCQOf_projSU_three_char_three (Or.inr rfl))
  nine_G2 := rowOf425_of_noCQ noCQOf_g2_three
  nine_SL4 := O.nine_SL4
  nine_SU4 := rowOf425_of_noCQ noCQOf_u43

theorem item4_25Fix_of_open
    (O : K425OpenRows) : Item4_25Fix :=
  item4_25Fix_of_rows (k425Rows_of_open O)

end Assembly

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
