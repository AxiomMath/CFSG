module

public import CFSG.Quasithin.Background.HSL3S77Fix

public section

namespace CFSG.Quasithin.H.S77

open Matrix

theorem span_th0 : ∀ x : Vec, x 0 = 0 → x ≠ 0 → ∀ z : Vec, z 0 = 0 →
    ∃ a b : ZMod 2, z = a • x + b • act th0 x := by decide +kernel

theorem span_th0d : ∀ y : Vec, y 0 = 0 → y ≠ 0 → ∀ z : Vec, z 0 = 0 →
    ∃ a b : ZMod 2, z = a • y + b • (th0d *ᵥ y) := by decide +kernel

end CFSG.Quasithin.H.S77
