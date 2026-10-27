module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Max

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan42_2a_max (T : Track Γ G) (F : FanTree Γ G) (h40 : Fan40 F) :
    ∃ a b : ℤ, IsMaxTArc T a b := by
  obtain ⟨a, b, -, -, hp, hmax⟩ := T.exists_pseg_max F
    (a₀ := 0) (b₀ := 1) ⟨by omega, fan42_1 T F h40 0⟩
  exact ⟨a, b, (fan42_2b T F h40 a b).2 ⟨hp, hmax⟩⟩

end CFSG.Quasithin.Fan86
