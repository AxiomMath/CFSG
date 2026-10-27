module

public import CFSG.Quasithin.Background.HSL3S77Model
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.H.S77

open Matrix

theorem trans_e1 : ∀ a : Vec, a ≠ 0 → ∃ h : SL32, act h e1 = a := by decide +kernel

end CFSG.Quasithin.H.S77
