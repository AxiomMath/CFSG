module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514RA2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514RB2

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_14 (F : FanTree Γ G)
    (h481 : Fan40 F → ∀ T₀ : Track Γ G, T₀.fixer ≠ ⊥ → ∃ T' : Track Γ G, InPiStar T')
    (h47 : Fan40 F → ∀ T : Track Γ G, TrackInPi T → ∀ a b c : ℤ, IsTArc T a b →
      (c = a ∨ c = b) → valence Γ (T.line.vert c) = 3)
    (h48len : Fan40 F → ∀ T : Track Γ G, InPiStar T → ∀ a b : ℤ, IsTArc T a b → b - a ≤ 8)
    (h49 : Fan40 F → ∀ T : Track Γ G, InPiStar T →
      ∃ d, valence Γ (T.line.vert d) = 5 ∧ ZT T d = ⊥)
    (h51a : Fan51a F) (h53b : Fan53b F) (h53c : Fan53c F) (h54 : Fan54 F) (h55a : Fan55a F)
    (h55b : Fan55b F) (h55c : Fan55c F) (h510 : Fan510 F) (h511 : Fan511 F)
    (h512cen : Fan512cen F) (h512b : Fan512b F) (h512c : Fan512c F) (h513a : Fan513a F) :
    Fan514 F := by
  intro h40 T z a tL tR hXi hz hz1 hc hval3
  by_cases hex : ∃ T' : Track Γ G, Xi 1 T'
  · exact P514.fan_5_14_xi1 F hex h47 h48len h49 h51a h53b h54 h510 h512cen h512b h40 T z a tL tR
      hXi hz hz1 hc hval3
  · push Not at hex
    have hT : ∀ T₀ : Track Γ G, T₀.fixer = ⊥ := fun T₀ => by
      by_contra h
      obtain ⟨T', hT'⟩ := h481 h40 T₀ h
      exact hex T' hT'
    exact P514.fan_5_14_empty F hex hT h51a h53b h53c h54 h55a h55b h55c h511 h512cen h512b
      h512c h513a h40 T z a tL tR hXi hz hz1 hc hval3

end CFSG.Quasithin.Fan86
