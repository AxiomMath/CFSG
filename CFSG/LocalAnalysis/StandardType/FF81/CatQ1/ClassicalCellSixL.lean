module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalCubeData
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalFrameL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_sl_order_nine_commute {n : ℕ} {F : Type*} [Field F] [Finite F] (hn : 6 ≤ n)
    {B : Matrix (Fin n) (Fin n) F} {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ X : SpecialLinearGroup (Fin n) F, (X : Matrix (Fin n) (Fin n) F) * B = B * X ∧ X ^ 9 = 1 ∧
      ∀ a : F, ((X ^ 3 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ a • 1 := by
  obtain ⟨P₁, P₂, S, hF⟩ := exists_isOrthogonalFrame_of_nonCube hn hB3 hc
  obtain ⟨lam, ω, j, hω, hω1, hlam⟩ := exists_cubeData_of_nonCube hc
  let R : Matrix (Fin n) (Fin n) F := orthRotation B P₁ P₂ lam ω j
  have hdet : R.det = 1 := hF.orthRotation_det hB3 hlam hω
  let X : SpecialLinearGroup (Fin n) F := ⟨R, hdet⟩
  refine ⟨X, ?_, ?_, ?_⟩
  · exact hF.orthRotation_commute
  · apply Subtype.ext
    change R ^ 9 = 1
    exact hF.orthRotation_pow_nine hB3 hlam hω
  · intro a h
    have hXR : ((X ^ 3 : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = R ^ 3 :=
      rfl
    exact (hF.orthRotation_pow_three_ne hB3 hlam hω hω1 a) (by simpa only [hXR] using h)

theorem exists_order_nine_fixed_of_nonCube {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 6 ≤ n)
    {B : GL (Fin n) F} {c : F}
    (hB3 : (B : Matrix (Fin n) (Fin n) F) ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ x : projectiveSL n F, orderOf x = 9 ∧ conjAut n F B x = x := by
  obtain ⟨X, hcomm, hX9, hX3⟩ := exists_sl_order_nine_commute hn hB3 hc
  refine ⟨proj n F X, ?_, ?_⟩
  · have hx9 : proj n F X ^ 9 = 1 := by rw [← map_pow, hX9, map_one]
    have hx3 : proj n F X ^ 3 ≠ 1 := by
      rw [← map_pow]
      intro h
      obtain ⟨d, -, hd⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
      refine hX3 (d : F) ?_
      rw [hd, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hnot : ¬ proj n F X ^ 3 ^ 1 = 1 := by simpa using hx3
    have hfin : proj n F X ^ 3 ^ (1 + 1) = 1 := by
      rw [show (3 : ℕ) ^ (1 + 1) = 9 from by norm_num]
      exact hx9
    have h := orderOf_eq_prime_pow hnot hfin
    rw [show (3 : ℕ) ^ (1 + 1) = 9 from by norm_num] at h
    exact h
  · rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, ← hcomm, mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, mul_one]

end CFSG.StandardType.FF81.CatQ1
