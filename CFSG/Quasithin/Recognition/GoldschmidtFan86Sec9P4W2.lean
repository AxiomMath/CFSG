module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4Shift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem isW1_of_isW1Elem_shift {w : G} (h : IsW1Elem (D.shift 2) w) : IsW1 D w := by
  obtain ⟨h1, -, h3, h4⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [← D.shift_x 2]; exact h3
  · rcases h4 with h | h
    · right
      simpa [D10Set.shift_delta] using h
    · left
      simpa [D10Set.shift_delta] using h

end D10Set

end CFSG.Quasithin.Fan86
