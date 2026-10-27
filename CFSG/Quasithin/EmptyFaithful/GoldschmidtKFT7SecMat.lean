module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.SBd19F

open Matrix

def slThreeTwoE12 : SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

def slThreeTwoE23 : SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

theorem slThreeTwoE12_mul_self : slThreeTwoE12 * slThreeTwoE12 = 1 := by decide

theorem slThreeTwoE23_mul_self : slThreeTwoE23 * slThreeTwoE23 = 1 := by decide

theorem slThreeTwoE_prod_pow_four : (slThreeTwoE12 * slThreeTwoE23) ^ 4 = 1 := by decide

private theorem dihedral_distinct_fin : ∀ (i j : Fin 4) (e d : Fin 2),
    (slThreeTwoE12 * slThreeTwoE23) ^ (i : ℕ) * slThreeTwoE12 ^ (e : ℕ) =
      (slThreeTwoE12 * slThreeTwoE23) ^ (j : ℕ) * slThreeTwoE12 ^ (d : ℕ) → i = j ∧ e = d := by
  decide

theorem slThreeTwoE_dihedral_distinct {i j e d : ℕ} (hi : i < 4) (hj : j < 4) (he : e < 2)
    (hd : d < 2)
    (h : (slThreeTwoE12 * slThreeTwoE23) ^ i * slThreeTwoE12 ^ e =
      (slThreeTwoE12 * slThreeTwoE23) ^ j * slThreeTwoE12 ^ d) : i = j ∧ e = d := by
  simpa [Fin.ext_iff] using dihedral_distinct_fin ⟨i, hi⟩ ⟨j, hj⟩ ⟨e, he⟩ ⟨d, hd⟩ h

end CFSG.Quasithin.SBd19F
