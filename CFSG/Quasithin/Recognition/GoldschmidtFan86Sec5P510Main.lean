module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P510Len
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan510 (F : FanTree Γ G) (h28 : Fan28) (h33 : Fan33 F) (h211 : Tutte.TutteTree)
    (h53a : Fan53a F) (h53b : Fan53b F) (h53c : Fan53c F) (h55c : Fan55c F) (h58b : Fan58b F)
    (h59 : Fan59 F) : Fan510 F := by
  intro h40 T hT z hz hz1
  have hPi : InPiStar T := hT.1
  have h48 : Fan48Two F := fan48_two F h40 h28 h211
  refine ⟨exists_coreFix F h40 h28 h33 h48 T hz hz1, ?_⟩
  intro a b tL tR hcore
  have hlen := zz_arc_length F h40 h28 h33 h211 T hPi hz hz1 hcore.fix
  have hC : T.line.IsCoreC z a b := h53b h40 T.line z a b hz hcore.core
  have hba : b - a ≤ 2 := h53c h40 T.line z a b (T.line.zz_subset_zc hz) hC
  have hab : a < b := hcore.core.1
  obtain ⟨hr1, hl1, -, -⟩ := h53a h40 T.line z a b tL tR hz hcore
  have h55 := abs_le.1 (h55c h40 T z z a b tL tR a b tL tR (T.line.zz_subset_zc hz)
    (T.line.zz_subset_zc hz) ⟨hcore.fix, hC⟩ ⟨hcore.fix, hC⟩)
  have key : b - a = 2 ∧ tR - b = a - tL := by
    by_cases he : (tR - tL) % 2 = 0
    · have g := h59 h40 T z hz hz1 a b tL tR hcore (Int.even_iff.2 he)
      omega
    · have h2 : tR - b ≤ 2 ∧ a - tL ≤ 2 := by omega
      exact h58b h40 T z a b tL tR hz hcore h2.1 h2.2
  exact ⟨key.1, key.2, by omega⟩

end CFSG.Quasithin.Fan86
