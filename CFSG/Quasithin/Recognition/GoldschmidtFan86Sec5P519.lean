module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtB

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan519 (F : FanTree Γ G) (h510 : Fan510 F) (h511 : Fan511 F) (h514 : Fan514 F)
    (h518 : Fan518 F) : Fan519 F := by
  intro h40 T hT z hz hz1
  obtain ⟨i, hi⟩ := hT
  by_cases hi1 : i = 1
  · subst hi1
    exact h510 h40 T hi z hz hz1
  · have h := h511 h40 i T hi1 hi z hz hz1
    refine ⟨h.1, fun a b tL tR hc => ?_⟩
    obtain ⟨hb, hr⟩ := h.2 a b tL tR hc
    obtain rfl : b = a + 2 := by omega
    refine ⟨hb, hr, ?_⟩
    by_cases hv : valence Γ (T.line.vert (a + 1)) = 3
    · have := h514 h40 T z a tL tR ⟨i, hi⟩ hz hz1 hc hv
      omega
    · have := h518 h40 T z a tL tR ⟨i, hi⟩ hz hz1 hc hv
      omega

end CFSG.Quasithin.Fan86
