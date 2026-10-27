
module


public import CFSG.Sporadic.Th.KernelSimple
public import CFSG.Assembly.Defs

@[expose] public section

namespace CFSG.Sporadic.Th

theorem a_sq_kernel : a ^ 2 = 1 := by
  rw [sq]
  exact Kernel.a_mul_a

theorem b_cube_kernel : b ^ 3 = 1 := by
  rw [pow_three, ← mul_assoc]
  exact Max3.AllConj.b_mul_b_mul_b

theorem x_sq_kernel : xJ ^ 2 = 1 := by
  rw [← ThSchreier.localX_eq, ThSchreier.localX_eq_word, sq]
  calc ((a * b) ^ 8)⁻¹ * a * (a * b) ^ 8 * (((a * b) ^ 8)⁻¹ * a * (a * b) ^ 8) =
      ((a * b) ^ 8)⁻¹ * (a * a) * (a * b) ^ 8 := by group
    _ = 1 := by rw [Kernel.a_mul_a]; group

end CFSG.Sporadic.Th
