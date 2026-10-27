module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Assembly
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RT1Suz
public import CFSG.RankThree.PartTwo.Sec14.Ronan148RT1L39
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Odd
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1F4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Ree
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1D4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1U4
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1Sp64

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K143OpenNoSuz : Prop where
  nine_SL3_nine : RowOf143 (projSL 3 (GaloisField 3 2))
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf143 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf143 (projSU 4 p 1)
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf143 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  eight_Sp6_4 : RowOf143 (projSp 3 (GaloisField 2 2))
  eight_SU5_8 : RowOf143 (projSU 5 2 3)
  eight_F4 : RowOf143 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

structure K143OpenLie : Prop where
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf143 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf143 (projSU 4 p 1)
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowOf143 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  eight_Sp6_4 : RowOf143 (projSp 3 (GaloisField 2 2))
  eight_SU5_8 : RowOf143 (projSU 5 2 3)
  eight_F4 : RowOf143 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

theorem K143OpenLie.toNoSuz (h : K143OpenLie) : K143OpenNoSuz where
  nine_SL3_nine := Ronan148R.rowOf143_l39
  four_G2 := h.four_G2
  four_SL := h.four_SL
  four_SU := h.four_SU
  seven_SU4 := h.seven_SU4
  seven_G2 := h.seven_G2
  seven_D4 := h.seven_D4
  seven_F4 := h.seven_F4
  eight_Sp6_4 := h.eight_Sp6_4
  eight_SU5_8 := h.eight_SU5_8
  eight_F4 := h.eight_F4

section Char2


structure K143OpenChar2 : Prop where
  eight_Sp6_4 : RowOf143 (projSp 3 (GaloisField 2 2))

theorem K143OpenChar2.toLie (h : K143OpenChar2) : K143OpenLie where
  four_G2 := Sec4.Ronan148L.kT1_four_G2
  four_SL := Sec4.Ronan148L.kT1_four_SL
  four_SU := Sec4.Ronan148L.kT1_four_SU
  eight_F4 := Sec4.Ronan148L.kT1_eight_F4
  seven_SU4 := Sec4.Ronan148L.kT1_seven_SU4
  seven_G2 := Sec4.Ronan148L.kT1_seven_G2
  seven_D4 := Sec4.Ronan148L.kT1_seven_D4
  seven_F4 := Sec4.Ronan148L.kT1_seven_F4
  eight_Sp6_4 := h.eight_Sp6_4
  eight_SU5_8 := Sec4.Ronan148L.kT1_eight_SU5_8

theorem k143OpenChar2_holds : K143OpenChar2 where
  eight_Sp6_4 := Sec4.Ronan148L.kT1_eight_Sp6_4

end Char2

section Suz


theorem K143OpenNoSuz.toK143Open (h : K143OpenNoSuz) : K143Open where
  suz := Ronan148R.rowOf143_spor_suz
  nine_SL3_nine := h.nine_SL3_nine
  four_G2 := h.four_G2
  four_SL := h.four_SL
  four_SU := h.four_SU
  seven_SU4 := h.seven_SU4
  seven_G2 := h.seven_G2
  seven_D4 := h.seven_D4
  seven_F4 := h.seven_F4
  eight_Sp6_4 := h.eight_Sp6_4
  eight_SU5_8 := h.eight_SU5_8
  eight_F4 := h.eight_F4

end Suz

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
