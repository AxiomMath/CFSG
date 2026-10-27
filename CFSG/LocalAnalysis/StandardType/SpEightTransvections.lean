module

public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem tvGL_mulVec (w x : Vec) :
    ((tvGL w : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ x = x + omega x w • w :=
  tvM_mulVec w x

theorem omega_smul_left_eq_mul (c : ZMod 2) (u v : Vec) : omega (c • u) v = c * omega u v := by
  simp [omega, smul_dotProduct, smul_eq_mul]

theorem omega_smul_right_eq_mul (c : ZMod 2) (u v : Vec) : omega u (c • v) = c * omega u v := by
  simp [omega, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem tvGL_mem_statedSp (w : Vec) : tvGL w ∈ StatedSp 4 (ZMod 2) := by
  rw [mem_statedSp_iff_omega]
  intro u v
  rw [tvGL_mulVec, tvGL_mulVec]
  simp only [omega_add_right, omega_add_left, omega_smul_left_eq_mul, omega_smul_right_eq_mul,
    omega_comm w v, omega_self w, mul_zero, add_zero, mul_comm (omega v w) (omega u w)]
  exact CharTwo.add_cancel_right _ _

theorem tvGL_mem_matrixOrthogonal {w : Vec} (hw : Q0 w = 1) : tvGL w ∈ matrixOrthogonal Q0 := by
  intro x
  rw [tvGL_mulVec]
  have hc : omega x w = 0 ∨ omega x w = 1 := by
    have h := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1)
    exact h (omega x w)
  rcases hc with h | h
  · rw [h, zero_smul, add_zero]
  · rw [h, one_smul, Q0_add, hw, h]
    exact CharTwo.add_cancel_right _ _

theorem mul_tvGL_mul_inv {g : GL Idx (ZMod 2)} (hg : g ∈ StatedSp 4 (ZMod 2)) (w : Vec) :
    g * tvGL w * g⁻¹ = tvGL ((g : Matrix Idx Idx (ZMod 2)) *ᵥ w) := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  set y : Vec := ((g⁻¹ : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ x with hy
  have hgy : (g : Matrix Idx Idx (ZMod 2)) *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have homega : omega y w = omega x ((g : Matrix Idx Idx (ZMod 2)) *ᵥ w) := by
    have h := (mem_statedSp_iff_omega g).mp hg y w
    rw [hgy] at h
    exact h.symm
  rw [tvGL_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hgy, homega, tvGL_mulVec]

end CFSG.StandardType.SpEight
