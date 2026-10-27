module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.H13

theorem ob5_dih_two_mul : ∀ a b : DihedralGroup 5, a * a = 1 → a ≠ 1 → b * b = 1 →
    ∃ k : ZMod 5, a * b = DihedralGroup.r k ∨ b = 1 := by
  decide

theorem ob5_dih_comm_inv : ∀ a b : DihedralGroup 5, a * a = 1 → a ≠ 1 → b * b = 1 →
    a * b = b * a → b = 1 ∨ b = a := by
  decide

end CFSG.Quasithin.H13
