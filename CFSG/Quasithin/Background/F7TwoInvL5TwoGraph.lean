module

public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.Quasithin.Background.F7TwoInvL5TwoElem

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GroupTheory.GL52 Matrix

@[expose] def gdual (g : G52) : G52 :=
  ⟨((g⁻¹ : G52) : M5).transpose, (g : M5).transpose,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩

theorem coe_gdual (g : G52) : ((gdual g : G52) : M5) = ((g⁻¹ : G52) : M5).transpose := rfl

theorem coe_gdual_inv (g : G52) : (((gdual g)⁻¹ : G52) : M5) = (g : M5).transpose := rfl

theorem gdual_gdual (g : G52) : gdual (gdual g) = g :=
  Units.ext (by rw [coe_gdual, coe_gdual_inv, Matrix.transpose_transpose])

theorem gdual_mul (g h : G52) : gdual (g * h) = gdual g * gdual h :=
  Units.ext (by
    simp only [coe_gdual, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

@[expose] def dualG : MulAut G52 where
  toFun := gdual
  invFun := gdual
  left_inv := gdual_gdual
  right_inv := gdual_gdual
  map_mul' := gdual_mul

theorem coe_dualG (g : G52) : ((dualG g : G52) : M5) = ((g⁻¹ : G52) : M5).transpose := rfl

theorem elemM_dual : ∀ i j : Fin 5, i ≠ j →
    ((elemM i j).transpose * elemM i j) ^ 3 = 1 ∧ (elemM i j).transpose * elemM i j ≠ 1 := by
  decide +kernel

theorem elem_mem_invXi_dualG {i j : Fin 5} (h : i ≠ j) : elem i j h ∈ invXiAut dualG := by
  rw [mem_invXiAut_iff]
  have hx : ((dualG (elem i j h) * (elem i j h)⁻¹ : G52) : M5) =
      (elemM i j).transpose * elemM i j := by
    simp only [Units.val_mul, coe_dualG, elem, coe_mk5_inv]
  obtain ⟨h3, h1⟩ := elemM_dual i j h
  refine pow_two_pow_ne_one_of_pow (s := 0) (m := 3) (by decide) ?_ ?_
  · refine Units.ext ?_
    simp only [Units.val_pow_eq_pow_val, hx, pow_zero, one_mul, Units.val_one]
    exact h3
  · intro h'
    rw [pow_zero, pow_one] at h'
    have := congrArg (fun g : G52 => (g : M5)) h'
    simp only [hx, Units.val_one] at this
    exact h1 this

theorem invAutGen_dualG : InvAutGen G52 dualG := by
  have hgen : Subgroup.closure {g : G52 | ∃ (i j : Fin 5) (h : i ≠ j), g = elem i j h} = ⊤ := by
    refine eq_top_of_elem_mem fun i j h => Subgroup.subset_closure ⟨i, j, h, rfl⟩
  refine invAutGen_of_seeds hgen ?_ ⟨elem 0 1 (by decide), ⟨0, 1, by decide, rfl⟩,
    elem_mem_invXi_dualG _⟩
  rintro _ ⟨i, j, h, rfl⟩
  exact Or.inl (elem_mem_invXi_dualG h)

end CFSG.Quasithin.F7Two
