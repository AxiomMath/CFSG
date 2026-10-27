
module

public import CFSG.Sporadic.Ly.Setup

@[expose] public section

namespace CFSG.Sporadic.Ly

open CFSG.Sporadic.LySchreier MulAction

theorem a_mul_self [LySeed] : a * a = 1 := by
  apply mat_injective
  rw [mat_mul, mat_a, mat_one]
  exact mA_sq

theorem a_inv [LySeed] : a⁻¹ = a := by
  rw [inv_eq_iff_mul_eq_one]
  exact a_mul_self

@[expose] noncomputable def genG [LySeed] (z : ℤ) : J :=
  if z = 1 then a else if z = -1 then a⁻¹ else if z = 2 then b else b⁻¹

noncomputable abbrev root : Fin 8835156 := ⟨0, by norm_num⟩

end CFSG.Sporadic.Ly
