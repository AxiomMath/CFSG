module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

structure K431OpenB : Prop where
  one_ge4 : ∀ e : ℕ, 4 ≤ e → RowSOf431 (projSL 2 (GaloisField 3 e))
  five_twelve : RowSOf431 (alternatingGroup (Fin 12))
  six_McL : RowSOf431 (Spor .McL)
  six_Ly : RowSOf431 (Spor .Ly)
  six_Suz : RowSOf431 (Spor .Suz)
  six_ONan : RowSOf431 (Spor .ONan)
  six_Co3 : RowSOf431 (Spor .Co3)
  six_Co2 : RowSOf431 (Spor .Co2)
  six_HN : RowSOf431 (Spor .HN)
  six_Th : RowSOf431 (Spor .Th)
  eight_SU5 : RowSOf431 (projSU 5 2 1)
  eight_SU6 : RowSOf431 (projSU 6 2 1)
  eight_Sp8 : RowSOf431 (projSp 4 (GaloisField 2 1))
  eight_OmegaPlus : RowSOf431 (projOmegaPlus 4 (GaloisField 2 1))
  eight_SU5_8 : RowSOf431 (projSU 5 2 3)
  nine_SL3_nine : RowSOf431 (projSL 3 (GaloisField 3 2))
  nine_SU3_nine : RowSOf431 (projSU 3 3 2)
  nine_SL4 : RowSOf431 (projSL 4 (GaloisField 3 1))

structure K431OpenC : Prop where
  seven_SL3 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSL 3 (GaloisField 2 n))
  seven_SU3 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 3 2 n)
  seven_Sp4_ne_three : ∀ n : ℕ, 1 ≤ n → n ≠ 3 → RowSOf431 (projSp 2 (GaloisField 2 n))
  seven_SU4 : ∀ n : ℕ, 1 ≤ n → RowSOf431 (projSU 4 2 n)
  seven_G2 : ∀ q : TauCeti.PrimePower, q.p = 2 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group
  seven_D4 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group
  seven_F4 : ∀ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid),
    RowSOf431 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group
  eight_SL6 : RowSOf431 (projSL 6 (GaloisField 2 1))
  eight_SL7 : RowSOf431 (projSL 7 (GaloisField 2 1))
  eight_OmegaMinus : ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
    RowSOf431 (projOmegaMinus 3 (GaloisField 2 1) b c)
  eight_SL4 : RowSOf431 (projSL 4 (GaloisField 2 2))
  eight_Sp6_4 : RowSOf431 (projSp 3 (GaloisField 2 2))
  eight_F4 : RowSOf431 (TauCeti.CFSGIndex.lie f4TwoIndex).Group

structure K431OpenD : Prop where
  four_SL_mod_one : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 1 →
    RowSOf431 (projSL 4 (GaloisField p 1))
  four_SU_mod_two : ∀ (p : ℕ) [Fact p.Prime], 3 < p → p % 3 = 2 → RowSOf431 (projSU 4 p 1)
  five_ten : RowSOf431 (alternatingGroup (Fin 10))
  five_eleven : RowSOf431 (alternatingGroup (Fin 11))

structure K431OpenW : Prop where
  one_27 : RowSOf431 (projSL 2 (GaloisField 3 3))
  nine_SU4 : RowSOf431 (projSU 4 3 1)

end CFSG.RankThree.PartTwo.Sec4.Ronan431
