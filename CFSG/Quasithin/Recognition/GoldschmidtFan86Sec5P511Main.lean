module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511One
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Odd
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P511Mid
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan511 (F : FanTree Γ G) (h28 : Fan28) (h33 : Fan33 F) (h211 : Tutte.TutteTree)
    (h53a : Fan53a F) (h53b : Fan53b F) (h53c : Fan53c F) (h55c : Fan55c F) (h57b : Fan57bT F)
    (h58b : Fan58b F) (h59 : Fan59 F) : Fan511 F := by
  intro h40 j T hj1 hT z hz hz1
  have h48 : Fan48Two F := fan48_two F h40 h28 h211
  refine ⟨exists_coreFix F h40 h28 h33 h48 T hz hz1, ?_⟩
  intro a b tL tR hcore
  have hC : T.line.IsCoreC z a b := h53b h40 T.line z a b hz hcore.core
  have hba : b - a ≤ 2 := h53c h40 T.line z a b (T.line.zz_subset_zc hz) hC
  have hab : a < b := hcore.core.1
  obtain ⟨hr1, hl1, -, -⟩ := h53a h40 T.line z a b tL tR hz hcore
  have h55 := abs_le.1 (h55c h40 T z z a b tL tR a b tL tR (T.line.zz_subset_zc hz)
    (T.line.zz_subset_zc hz) ⟨hcore.fix, hC⟩ ⟨hcore.fix, hC⟩)
  by_cases he : (tR - tL) % 2 = 0
  · have g := h59 h40 T z hz hz1 a b tL tR hcore (Int.even_iff.2 he)
    exact ⟨g, by omega⟩
  · exfalso
    have hodd : (tR - tL) % 2 = 1 := by omega
    have hLR : tL ≤ tR := by
      obtain ⟨-, hc, -, -⟩ := (T.line.isCore_iff).1 hcore.core
      have := (hcore.fix a).1 ((T.line.mem_edgeStab_iff).1 (hc a le_rfl hab).1).1
      omega
    obtain ⟨T'', hT''⟩ := exists_hasReflections_of_odd F T hz.1 hcore.fix hLR hodd
    have hTrefl : T.HasReflections := by
      obtain ⟨hX, hmin⟩ := hT
      rcases j with _ | _ | _ | _ | n
      · exact hX.elim
      · exact absurd rfl hj1
      · exact hX
      · exact (hmin 2 (by norm_num) (by norm_num) ⟨T'', hT''⟩).elim
      · exact hX.elim
    by_cases hb2 : b - a = 2
    · obtain rfl : b = a + 2 := by omega
      obtain ⟨f, hf⟩ := hTrefl (a + 1)
      have := even_of_core_two F T hcore hf
      omega
    · obtain rfl : b = a + 1 := by omega
      exact core_one_false F h40 T hTrefl h53b h57b h58b hz hcore (by omega)

end CFSG.Quasithin.Fan86
