module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p m : ℕ} (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p))

@[expose] def orthReflLin (v : Fin m → ZMod p) : (Fin m → ZMod p) →ₗ[ZMod p] (Fin m → ZMod p) :=
  LinearMap.id + (f.flip v).smulRight v

theorem orthReflLin_apply (v x : Fin m → ZMod p) : orthReflLin f v x = x + f x v • v := by
  simp [orthReflLin]

private theorem orthReflLin_neg_norm (v : Fin m → ZMod p) : f (-v) (-v) = f v v := by
  rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]

theorem orthReflLin_mul_self {v : Fin m → ZMod p} (hv : f v v = -2) :
    orthReflLin f v * orthReflLin f v = 1 := by
  apply LinearMap.ext
  intro x
  change orthReflLin f v (orthReflLin f v x) = x
  rw [orthReflLin_apply, orthReflLin_apply]
  have hval : f (x + f x v • v) v = f x v + f x v * f v v := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  have hc : f x v + f x v * (-2 : ZMod p) = -f x v := by ring
  rw [hval, hv, hc, neg_smul, add_assoc, add_neg_cancel, add_zero]

theorem toMatrix'_orthReflLin_mul_self {v : Fin m → ZMod p} (hv : f v v = -2) :
    LinearMap.toMatrix' (orthReflLin f v) * LinearMap.toMatrix' (orthReflLin f v) = 1 := by
  rw [← LinearMap.toMatrix'_mul, orthReflLin_mul_self f hv, LinearMap.toMatrix'_one]

@[expose] def orthRefl (v : Fin m → ZMod p) : GL (Fin m) (ZMod p) :=
  if hv : f v v = -2 then
    ⟨LinearMap.toMatrix' (orthReflLin f v), LinearMap.toMatrix' (orthReflLin f v),
      toMatrix'_orthReflLin_mul_self f hv, toMatrix'_orthReflLin_mul_self f hv⟩
  else 1

theorem orthRefl_mulVec {v : Fin m → ZMod p} (hv : f v v = -2) (x : Fin m → ZMod p) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x = x + f x v • v := by
  rw [orthRefl, dif_pos hv]
  change LinearMap.toMatrix' (orthReflLin f v) *ᵥ x = x + f x v • v
  rw [LinearMap.toMatrix'_mulVec, orthReflLin_apply]

theorem orthRefl_mem {v : Fin m → ZMod p} (hv : f v v = -2) : orthRefl f v ∈ orthReflSet p m f :=
  ⟨v, hv, orthRefl_mulVec f hv⟩

theorem gl_ext_mulVec {g h : GL (Fin m) (ZMod p)}
    (H : ∀ x, (g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x =
      (h : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) :
    g = h := by
  exact Units.ext (Matrix.ext_iff_mulVec.mpr H)

theorem exists_eq_orthRefl_of_mem {g : GL (Fin m) (ZMod p)} (hg : g ∈ orthReflSet p m f) :
    ∃ v, f v v = -2 ∧ g = orthRefl f v := by
  obtain ⟨v, hv, hgv⟩ := hg
  exact ⟨v, hv, gl_ext_mulVec fun x => by rw [hgv x, orthRefl_mulVec f hv x]⟩

theorem orthRefl_mul_self {v : Fin m → ZMod p} (hv : f v v = -2) :
    orthRefl f v * orthRefl f v = 1 := by
  rw [orthRefl, dif_pos hv]
  apply Units.ext
  exact toMatrix'_orthReflLin_mul_self f hv

theorem orthRefl_inv (v : Fin m → ZMod p) : (orthRefl f v)⁻¹ = orthRefl f v := by
  by_cases hv : f v v = -2
  · rw [orthRefl, dif_pos hv]
    apply Units.ext
    rfl
  · rw [show orthRefl f v = 1 from by simp only [orthRefl, dif_neg hv], inv_one]

theorem orthRefl_neg (v : Fin m → ZMod p) : orthRefl f (-v) = orthRefl f v := by
  by_cases hv : f v v = -2
  · have hv' : f (-v) (-v) = -2 := by rw [orthReflLin_neg_norm, hv]
    refine gl_ext_mulVec fun x => ?_
    rw [orthRefl_mulVec f hv' x, orthRefl_mulVec f hv x,
      LinearMap.BilinForm.neg_right, neg_smul, smul_neg, neg_neg]
  · have hv' : ¬(f (-v) (-v) = -2) := by rw [orthReflLin_neg_norm]; exact hv
    rw [show orthRefl f (-v) = 1 from by simp only [orthRefl, dif_neg hv'],
      show orthRefl f v = 1 from by simp only [orthRefl, dif_neg hv]]

private theorem toMatrix'_orthReflLin_eq (v : Fin m → ZMod p) :
    LinearMap.toMatrix' (orthReflLin f v) =
      1 + replicateCol Unit v * replicateRow Unit (fun j => f (Pi.single j 1) v) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, orthReflLin_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.mul_apply]
  simp [replicateCol_apply, replicateRow_apply, Pi.single_apply, smul_eq_mul, mul_comm]

private theorem dotProduct_orthReflLin (v : Fin m → ZMod p) :
    (fun j => f (Pi.single j 1) v) ⬝ᵥ v = f v v := by
  have hsingle : ∀ j : Fin m, (fun k => if j = k then (1 : ZMod p) else 0) = Pi.single j 1 := by
    intro j
    funext k
    rw [Pi.single_apply]
    by_cases h : j = k
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hv : v = ∑ j, v j • Pi.single j 1 := by
    conv_lhs => rw [pi_eq_sum_univ v]
    exact Finset.sum_congr rfl fun j _ => by rw [hsingle j]
  have hvv : f v v = ∑ j, v j * f (Pi.single j 1) v := by
    conv_lhs => arg 1; arg 2; rw [hv]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc (fun j => f (Pi.single j 1) v) ⬝ᵥ v
      = ∑ j, v j * f (Pi.single j 1) v := by
        simp only [dotProduct]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = f v v := hvv.symm

theorem orthRefl_det {v : Fin m → ZMod p} (hv : f v v = -2) :
    (orthRefl f v : Matrix (Fin m) (Fin m) (ZMod p)).det = -1 := by
  rw [orthRefl, dif_pos hv]
  change (LinearMap.toMatrix' (orthReflLin f v)).det = -1
  rw [toMatrix'_orthReflLin_eq f v, Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_orthReflLin f v, hv]
  ring

theorem orthRefl_ne_one [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) {v : Fin m → ZMod p}
    (hv : f v v = -2) : orthRefl f v ≠ 1 := by
  intro h
  have hd := orthRefl_det f hv
  rw [h, Matrix.GeneralLinearGroup.coe_one, Matrix.det_one] at hd
  exact h2 (by linear_combination hd)

theorem orthRefl_comm (hf : ∀ x y, f x y = f y x) {u v : Fin m → ZMod p} (huv : f u v = 0) :
    orthRefl f u * orthRefl f v = orthRefl f v * orthRefl f u := by
  by_cases hu : f u u = -2
  · by_cases hv : f v v = -2
    · have hvu : f v u = 0 := by rw [hf v u, huv]
      refine gl_ext_mulVec fun x => ?_
      have h1 : f (x + f x v • v) u = f x u := by
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvu]
      have h2 : f (x + f x u • u) v = f x v := by
        simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huv]
      simp only [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      rw [orthRefl_mulVec f hv x, orthRefl_mulVec f hu (x + f x v • v),
        orthRefl_mulVec f hu x, orthRefl_mulVec f hv (x + f x u • u), h1, h2]
      abel
    · rw [show orthRefl f v = 1 from by simp only [orthRefl, dif_neg hv], mul_one, one_mul]
  · rw [show orthRefl f u = 1 from by simp only [orthRefl, dif_neg hu], one_mul, mul_one]

@[expose] def IsOrthIsometry (g : GL (Fin m) (ZMod p)) : Prop :=
  ∀ x y, f ((g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x)
    ((g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ y) = f x y

theorem isOrthIsometry_one : IsOrthIsometry f 1 := by
  intro x y
  rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, Matrix.one_mulVec]

theorem IsOrthIsometry.mul {f} {g h : GL (Fin m) (ZMod p)} (hg : IsOrthIsometry f g)
    (hh : IsOrthIsometry f h) : IsOrthIsometry f (g * h) := by
  intro x y
  simp only [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  exact (hg _ _).trans (hh x y)

theorem IsOrthIsometry.inv {f} {g : GL (Fin m) (ZMod p)} (hg : IsOrthIsometry f g) :
    IsOrthIsometry f g⁻¹ := by
  intro x y
  have h := hg ((g⁻¹ : GL (Fin m) (ZMod p)) *ᵥ x) ((g⁻¹ : GL (Fin m) (ZMod p)) *ᵥ y)
  simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
  exact h.symm

theorem isOrthIsometry_orthRefl (hf : ∀ x y, f x y = f y x) (v : Fin m → ZMod p) :
    IsOrthIsometry f (orthRefl f v) := by
  intro x y
  by_cases hv : f v v = -2
  · rw [orthRefl_mulVec f hv x, orthRefl_mulVec f hv y]
    have hfy : f v y = f y v := hf v y
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hv, hfy]
    ring
  · rw [show orthRefl f v = 1 from by simp only [orthRefl, dif_neg hv],
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, Matrix.one_mulVec]

theorem isOrthIsometry_of_mem_closure (hf : ∀ x y, f x y = f y x) {g : GL (Fin m) (ZMod p)}
    (hg : g ∈ Subgroup.closure (orthReflSet p m f)) : IsOrthIsometry f g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := exists_eq_orthRefl_of_mem f hx
      exact isOrthIsometry_orthRefl f hf v
  | one => exact isOrthIsometry_one f
  | mul x y _ _ ihx ihy => exact ihx.mul ihy
  | inv x _ ih => exact ih.inv

theorem orthRefl_conj {f} {g : GL (Fin m) (ZMod p)} (hg : IsOrthIsometry f g) (v : Fin m → ZMod p) :
    g * orthRefl f v * g⁻¹ = orthRefl f ((g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) := by
  by_cases hv : f v v = -2
  · have hgv : f (↑g *ᵥ v) (↑g *ᵥ v) = -2 := by rw [hg, hv]
    refine gl_ext_mulVec fun x => ?_
    have hx : f ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) v = f x (↑g *ᵥ v) := by
      have h := hg ((↑g⁻¹ : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) v
      simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] at h
      exact h.symm
    have hL : (↑(g * orthRefl f v * g⁻¹) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x
        = x + f x (↑g *ᵥ v) • (↑g *ᵥ v) := by
      simp only [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
        orthRefl_mulVec f hv, Matrix.mulVec_add, Matrix.mulVec_smul, hx]
      rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    rw [hL, orthRefl_mulVec f hgv]
  · have hgv : ¬(f (↑g *ᵥ v) (↑g *ᵥ v) = -2) := by rw [hg]; exact hv
    rw [show orthRefl f v = 1 from by simp only [orthRefl, dif_neg hv],
      show orthRefl f (↑g *ᵥ v) = 1 from by simp only [orthRefl, dif_neg hgv]]
    simp

end CFSG.LocalAnalysis.WeakClosure81
