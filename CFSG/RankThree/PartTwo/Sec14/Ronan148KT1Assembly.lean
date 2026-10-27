module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowAlt
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowL2
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowL3
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowSp4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowEight

public section
namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K143Open : Prop where
  suz : RowOf143 (Sec4.Spor .Suz)
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

theorem mem_sporadics42_cases (s : TauCeti.SporadicName) (hs : s ∈ sporadics42) :
    s = TauCeti.SporadicName.M11 ∨ s = TauCeti.SporadicName.M12 ∨
    s = TauCeti.SporadicName.M22 ∨ s = TauCeti.SporadicName.M23 ∨
    s = TauCeti.SporadicName.M24 ∨ s = TauCeti.SporadicName.J1 ∨
    s = TauCeti.SporadicName.J2 ∨ s = TauCeti.SporadicName.J3 ∨
    s = TauCeti.SporadicName.J4 ∨ s = TauCeti.SporadicName.McL ∨
    s = TauCeti.SporadicName.Ly ∨ s = TauCeti.SporadicName.HS ∨
    s = TauCeti.SporadicName.He ∨ s = TauCeti.SporadicName.Suz ∨
    s = TauCeti.SporadicName.Ru ∨ s = TauCeti.SporadicName.ONan ∨
    s = TauCeti.SporadicName.Co3 ∨ s = TauCeti.SporadicName.Co2 ∨
    s = TauCeti.SporadicName.HN ∨ s = TauCeti.SporadicName.Th := by
  simpa [sporadics42] using hs

theorem k143Rows_of_open
    (h : K143Open) : K143Rows := by
  obtain ⟨h2SL, h2SU, h7SL3, h7SU3⟩ := k143_rows_three
  have six : ∀ s ∈ sporadics42, RowOf143 (Spor s) := by
    intro s hs
    rcases mem_sporadics42_cases s hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rowOf143_spor_m11
    · exact rowOf143_spor_m12
    · exact rowOf143_spor_m22
    · exact rowOf143_spor_m23
    · exact rowOf143_spor_m24
    · exact rowOf143_spor_j1
    · exact rowOf143_spor_j2
    · exact rowOf143_spor_j3
    · exact rowOf143_spor_j4
    · exact rowOf143_spor_mcl
    · exact rowOf143_spor_ly
    · exact rowOf143_spor_hs
    · exact rowOf143_spor_he
    · exact h.suz
    · exact rowOf143_spor_ru
    · exact rowOf143_spor_on
    · exact rowOf143_spor_co3
    · exact rowOf143_spor_co2
    · exact rowOf143_spor_hn
    · exact rowOf143_spor_th
  have nine_SL3 : ∀ e : ℕ, 1 ≤ e → e ≤ 3 → RowOf143 (projSL 3 (GaloisField 3 e)) := by
    intro e he he3
    by_cases he2 : e = 2
    · subst he2
      exact h.nine_SL3_nine
    · exact rowOf143_l3_three e he he3 he2
  exact
    { one := fun p e _ _ he => rowOf143_psl2 p e he
      two_SL := h2SL
      two_SU := h2SU
      three := fun hr => rowOf143_ree27 hr
      four_G2 := h.four_G2
      four_Sp := fun p _ hp => rowOf143_psp4_prime p hp
      four_SL := h.four_SL
      four_SU := h.four_SU
      five := fun n hn5 hn12 => rowOf143_alt n hn5 hn12
      six := six
      seven_SL2 := fun n hn => rowOf143_psl2 2 n hn
      seven_SL3 := h7SL3
      seven_SU3 := h7SU3
      seven_Sp4 := fun n hn => rowOf143_sp4_two n hn
      seven_SU4 := h.seven_SU4
      seven_G2 := h.seven_G2
      seven_D4 := h.seven_D4
      seven_Sz := fun m hm => rowOf143_suzuki m hm
      seven_F4 := h.seven_F4
      seven_Tits := fun ht => rowOf143_seven_Tits ht
      eight_SL5 := rowOf143_eight_SL5
      eight_SU5 := rowOf143_eight_SU5
      eight_SL6 := rowOf143_eight_SL6
      eight_SU6 := rowOf143_eight_SU6
      eight_SL7 := rowOf143_eight_SL7
      eight_Sp6 := rowOf143_eight_Sp6
      eight_Sp8 := rowOf143_eight_Sp8
      eight_OmegaPlus := rowOf143_eight_OmegaPlus
      eight_OmegaMinus := fun b c hbc => rowOf143_eight_OmegaMinus b c hbc
      eight_SL4 := rowOf143_eight_SL4
      eight_Sp6_4 := h.eight_Sp6_4
      eight_SU5_4 := rowOf143_eight_SU5_4
      eight_SU5_8 := h.eight_SU5_8
      eight_F4 := h.eight_F4
      nine_SL3 := nine_SL3
      nine_SU3 := fun e he he3 => rowOf143_u3_three e he he3
      nine_G2 := rowOf143_g2_three
      nine_SL4 := rowOf143_l4_three
      nine_SU4 := rowOf143_u4_three }

theorem ks143LBalComp2_of_open
    (h1 : Sec4.Item4_1LargePrime) (h : K143Open) : KS143LBalComp2 :=
  ks143LBalComp2_of_k143Rows h1 (k143Rows_of_open h)

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
