module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.H13.U43

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 200000 in
theorem A6_dihedral_cyclic : ∀ u v : alternatingGroup (Fin 6), u ^ 2 = 1 → v ^ 4 = 1 →
    v ^ 2 ≠ 1 → u * v * u⁻¹ = v⁻¹ →
    (∃ m : alternatingGroup (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = u * m ∧ m * u = (v ^ 2 * u) * m) ∧
    (∃ m : alternatingGroup (Fin 6), m ^ 3 = 1 ∧ m * v ^ 2 = (u * v) * m ∧
      m * (u * v) = (v ^ 2 * (u * v)) * m) := by
  decide +kernel

end CFSG.Quasithin.H13.U43
