module

public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GroupTheory

theorem mul_mul_conj_mem_of_normal {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal]
    {k a : G} (hk : k ∈ N) (ha : a * a = 1) : a * (k * a * k⁻¹) ∈ N := by
  simpa [inv_eq_of_mul_eq_one_right ha, mul_assoc] using
    N.mul_mem (hN.conj_mem k hk a) (N.inv_mem hk)

end CFSG.GroupTheory
