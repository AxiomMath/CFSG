module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersSporadic
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Vol2.Ch10SecA312C3

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312C

open CFSG.Open CFSG.Quasithin CFSG.Blueprint

variable {Y : Type} [Group Y]

theorem card_l32 (h : IsPSL 3 2 1 Y) : Nat.card Y = 168 := by rw [card_of_isPSL h]; decide
theorem card_l34 (h : IsPSL 3 2 2 Y) : Nat.card Y = 20160 := by rw [card_of_isPSL h]; decide
theorem card_l42 (h : IsPSL 4 2 1 Y) : Nat.card Y = 20160 := by rw [card_of_isPSL h]; decide
theorem card_l52 (h : IsPSL 5 2 1 Y) : Nat.card Y = 9999360 := by rw [card_of_isPSL h]; decide

theorem card_u35 (h : IsPSU 3 5 1 Y) : Nat.card Y = 126000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_five h

theorem card_su35 (h : IsSU3 5 Y) : Nat.card Y = 378000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [card_of_isSU3 h]
  norm_num

theorem card_alt5 (h : IsAlt 5 Y) : Nat.card Y = 60 := by rw [card_of_isAlt (by norm_num) h]; rfl
theorem card_alt6 (h : IsAlt 6 Y) : Nat.card Y = 360 := by rw [card_of_isAlt (by norm_num) h]; rfl
theorem card_alt7 (h : IsAlt 7 Y) : Nat.card Y = 2520 := by
  rw [card_of_isAlt (by norm_num) h]; rfl

theorem card_hat6 (h : IsHat Y (alternatingGroup (Fin 6))) : Nat.card Y = 1080 := by
  rw [card_of_isHat h, card_alt6 ⟨MulEquiv.refl _⟩]
theorem card_hat7 (h : IsHat Y (alternatingGroup (Fin 7))) : Nat.card Y = 7560 := by
  rw [card_of_isHat h, card_alt7 ⟨MulEquiv.refl _⟩]

theorem card_m11 (h : IsSporadic .M11 Y) : Nat.card Y = 7920 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M11
theorem card_m22 (h : IsSporadic .M22 Y) :
    Nat.card Y = 443520 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M22
theorem card_hatm22
    (h : IsHat Y (NativeSporadic.Carrier .M22)) : Nat.card Y = 1330560 := by
  rw [card_of_isHat h]
  change 3 * Nat.card NativeSporadic.M22 = _
  rw [CFSG.Sporadic.Mathieu.card_M22]
theorem card_m24 (h : IsSporadic .M24 Y) :
    Nat.card Y = 244823040 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M24
theorem card_j1 (h : IsSporadic .J1 Y) : Nat.card Y = 175560 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.J1.card_J1
theorem card_j4 (h : IsSporadic .J4 Y) :
    Nat.card Y = 86775571046077562880 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.J4.card_J4
theorem card_hs (h : IsSporadic .HS Y) :
    Nat.card Y = 44352000 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.HS.card_HS
theorem card_ru (h : IsSporadic .Ru Y) :
    Nat.card Y = 145926144000 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.Ru.card_Ru
theorem card_he (h : IsSporadic .He Y) :
    Nat.card Y = 4030387200 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.Sporadic.He.card_He

theorem card_m23
    (h : IsSporadic .M23 Y) : Nat.card Y = 10200960 := by
  obtain ⟨φ⟩ := h; rw [Nat.card_congr φ.toEquiv]; exact CFSG.EvenSmallLie.CatalogOrders.card_M23

end CFSG.Quasithin.Vol2.Ch10.A312C
