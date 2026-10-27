module

public import CFSG.Quasithin.Background.HSL3S77Blk

public section

namespace CFSG.Quasithin.H.S77

theorem gl2_comm_pow_three : ∀ a b : GL (Fin 2) (ZMod 2), (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := by
  decide +kernel

theorem gl2_pow_three_of_comm : ∀ a b : GL (Fin 2) (ZMod 2), a ^ 3 = 1 → a ≠ 1 → a * b = b * a →
    b ^ 3 = 1 := by
  decide +kernel

theorem gl2_pow_six : ∀ b : GL (Fin 2) (ZMod 2), b ^ 6 = 1 := by
  decide +kernel

theorem gl2_cube_cases : ∀ a b : GL (Fin 2) (ZMod 2), a ^ 3 = 1 → a ≠ 1 → b ^ 3 = 1 →
    b = 1 ∨ b = a ∨ b = a * a := by
  decide +kernel

theorem blk_th0_ne_one : blk th0 ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.H.S77
