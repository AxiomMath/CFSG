module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem IsFFStarOffender.isFFModule {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    IsFFModule X := by
  obtain ⟨hAX, hA1, hAe, hB⟩ := hA
  refine ⟨A, hAX, hA1, hAe, ?_⟩
  have h := hB ⊥ bot_le
  have hfix : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
    ext v
    simp only [mem_fixV, Subgroup.mem_bot, Subgroup.mem_top, iff_true]
    rintro x rfl
    rfl
  rwa [Subgroup.card_bot, one_mul, hfix, Subgroup.card_top] at h

end CFSG.Quasithin
