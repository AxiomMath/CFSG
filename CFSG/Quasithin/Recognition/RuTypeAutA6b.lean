module

public import CFSG.Quasithin.Recognition.RuTypeAutA6

public section

namespace CFSG.Quasithin.RuType.AutA6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts

@[expose] def wInv : P10 := A6Models.perm10 [[0, 6], [2, 8], [3, 5], [4, 9]]

theorem wInv_mem_psl29 : wInv ∈ A6Models.psl29 := by
  rw [mem_psl29_iff]
  decide +kernel

theorem wInv_mul_self : wInv * wInv = 1 := by decide +kernel

theorem wInv_ne_one : wInv ≠ 1 := by decide +kernel

theorem wInv_comm_dInv : wInv * dInv = dInv * wInv := by decide +kernel

theorem wInv_inv_x5 : wInv * (A6Models.tAdd * A6Models.tSq * A6Models.tInv) * wInv⁻¹ =
    (A6Models.tAdd * A6Models.tSq * A6Models.tInv)⁻¹ := by decide +kernel

end CFSG.Quasithin.RuType.AutA6
