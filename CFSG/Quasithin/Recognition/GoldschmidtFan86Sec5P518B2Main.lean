module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2LowMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Orb4
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Fin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Core

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem nOrb_eq_four (S : B2Set F L T a) : nOrb T a = 4 := by
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence (xv T a 6)
  have hv : valence Γ (xv T a 6) = 5 := by simpa using S.val_even 3
  have hxo5 : orderOf x = 5 := by rw [hxo, hv]
  exact nOrb_eq_four_of_lowerBound S hx hxo5 (lowerBound S hx hxo5)

theorem b2_unc (S : B2Set F L T a) :
    zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1 :=
  b2_of_ctx S (nOrb_eq_four S)

end P518

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_5_18_proved (F : FanTree Γ G) (h33 : Fan33 F) (h36 : Fan36 F)
    (h481 : Fan40 F → ∀ T₀ : Track Γ G, T₀.fixer ≠ ⊥ → ∃ T' : Track Γ G, InPiStar T')
    (h510 : Fan510 F) (h511 : Fan511 F) (h512cen : Fan512cen F) (h512b : Fan512b F)
    (h512c : Fan512c F) (h515a : Fan515a F) (h516 : Fan516 F) (h517a : Fan517a F)
    (h517c : Fan517c F) (hD : LemmaD F) : Fan518 F :=
  fan_5_18_core F (fun _ _ _ S => P518.b2_unc S) h33 h36 h481 h510 h511 h512cen h512b h512c
    h515a h516 h517a h517c hD

end CFSG.Quasithin.Fan86
