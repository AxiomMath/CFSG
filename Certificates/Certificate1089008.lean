module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.Bound.Init

public section

namespace Certificates

set_option maxHeartbeats 0 in
theorem certificate1089008 : ∀ a b : Equiv.Perm (Fin 5), a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 →
    (a * b) ^ 3 = 1 → a * b ≠ 1 →
    (Finset.univ.filter fun π : Equiv.Perm (Fin 5) =>
      π * a * π⁻¹ = a ∧ π * b * π⁻¹ = b).card ≤ 2 :=
  by decide +kernel

end Certificates
