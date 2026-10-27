module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SAssembly
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RHe

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K425OpenRowsLie : Prop where
  two_SL : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    RowOf425 (projSL 3 (GaloisField p e))
  two_SU : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 → RowOf425 (projSU 3 p e)
  four_G2 : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf425 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  four_Sp : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSp 2 (GaloisField p 1))
  four_SL : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSL 4 (GaloisField p 1))
  four_SU : ∀ (p : ℕ) [Fact p.Prime], 3 < p → RowOf425 (projSU 4 p 1)
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

section RowHe


theorem K425OpenRowsLie.toOpen
    (h : K425OpenRowsLie) : K425OpenRows where
  six_open s hs := by
    simp only [sporadicsOpen425, List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst hs
    exact Ronan148R.rowOf425_he
  two_SL := h.two_SL
  two_SU := h.two_SU
  four_G2 := h.four_G2
  four_Sp := h.four_Sp
  four_SL := h.four_SL
  four_SU := h.four_SU
  seven_SL3 := h.seven_SL3
  seven_SU3 := h.seven_SU3
  seven_Sp4 := h.seven_Sp4
  seven_SU4 := h.seven_SU4
  seven_G2 := h.seven_G2
  seven_D4 := h.seven_D4
  seven_F4 := h.seven_F4
  seven_Tits := h.seven_Tits
  eight_SU5 := h.eight_SU5
  eight_SL6 := h.eight_SL6
  eight_SU6 := h.eight_SU6
  eight_SL7 := h.eight_SL7
  eight_Sp6 := h.eight_Sp6
  eight_Sp8 := h.eight_Sp8
  eight_OmegaPlus := h.eight_OmegaPlus
  eight_OmegaMinus := h.eight_OmegaMinus
  eight_SL4 := h.eight_SL4
  eight_Sp6_4 := h.eight_Sp6_4
  eight_SU5_8 := h.eight_SU5_8
  eight_F4 := h.eight_F4
  nine_SL3_nine := h.nine_SL3_nine
  nine_SU3_nine := h.nine_SU3_nine
  nine_SL4 := h.nine_SL4

end RowHe

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
