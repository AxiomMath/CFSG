module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem transvection_mulVec_eq_add (a b : Fin 6) (c : K) (v : Fin 6 → K) :
    Matrix.transvection a b c *ᵥ v = v + Pi.single a (c * v b) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  congr 1

theorem transvGL_mulVec_e_of_ne {a b j : Fin 6} (hab : a ≠ b) (hj : j ≠ b) :
    (transvGL K a b hab 1 : Matrix (Fin 6) (Fin 6) K) *ᵥ e K j = e K j := by
  rw [transvGL_val, transvection_mulVec_eq_add]
  have h0 : e K j b = 0 := by
    simp [e, Pi.single_apply, Ne.symm hj]
  rw [h0, mul_zero, Pi.single_zero, add_zero]

theorem transvGL_mulVec_e_self {a b : Fin 6} (hab : a ≠ b) :
    (transvGL K a b hab 1 : Matrix (Fin 6) (Fin 6) K) *ᵥ e K b = e K b + e K a := by
  rw [transvGL_val, transvection_mulVec_eq_add]
  have h0 : e K b b = 1 := by
    simp [e]
  rw [h0, mul_one]

end CFSG.RankThree.GF2n.Smith81.A5Cube
