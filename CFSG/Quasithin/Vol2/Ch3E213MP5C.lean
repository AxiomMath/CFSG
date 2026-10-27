module

public import CFSG.Quasithin.Vol2.Ch3E213MP5B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k]

theorem map_symm_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (X : Subgroup G) :
    (X.map e.toMonoidHom).map e.symm.toMonoidHom = X := by
  ext x
  simp

theorem map_map_symm {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (X : Subgroup G') :
    (X.map e.symm.toMonoidHom).map e.toMonoidHom = X := by
  ext x
  simp

variable (k) in
@[expose] def wz : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨!![0, 0, 1; 0, -1, 0; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

theorem wz_mul_self : wz k * wz k = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wz, Matrix.mul_apply, Fin.sum_univ_three]

theorem coe_wz_conj : ((wz k * uu 1 0 0 * (wz k)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
    Matrix (Fin 3) (Fin 3) k) = !![1, 0, 0; 0, 1, 0; 0, -1, 1] := by
  rw [inv_eq_of_mul_eq_one_right wz_mul_self, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wz, Matrix.mul_apply, Fin.sum_univ_three]

theorem normalizer_pa1_ne_top :
    Subgroup.normalizer (pa1 k : Set (projectiveSL 3 k)) ≠ ⊤ := by
  intro h
  have hw : proj 3 k (wz k) ∈ Subgroup.normalizer (pa1 k : Set (projectiveSL 3 k)) :=
    h ▸ Subgroup.mem_top _
  have h1 : proj 3 k (wz k * uu 1 0 0 * (wz k)⁻¹) ∈ pa1 k := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hw _).1 ⟨uu 1 0 0, ⟨1, 0, rfl⟩, rfl⟩
  obtain ⟨_, ⟨a, c, rfl⟩, hu⟩ := h1
  obtain ⟨s, -, hs⟩ := proj_eq_proj_iff.mp hu
  have hy : ((wz k * uu 1 0 0 * (wz k)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) =
        (uu a 0 c : Matrix (Fin 3) (Fin 3) k) * scalar (Fin 3) (s : k) := by
    rw [← hs, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h21 := congrFun (congrFun hy 2) 1
  rw [coe_wz_conj] at h21
  simp [coe_uu, Matrix.mul_apply, Fin.sum_univ_three] at h21

theorem normalizer_pa1_eq [Finite k] (hk : ∃ m : ℕ, Nat.card k = 2 ^ m) :
    Subgroup.normalizer (pa1 k : Set (projectiveSL 3 k)) = projStabilizer (flagSpace 3 k 1) := by
  have hR := CFSG.QuasithinUnique.Setup.X7a.linear_three_residualOvergroupsAt hk
  have hcov : projStabilizer (flagSpace 3 k 1) ⋖ ⊤ := by
    have h := (hR.2.2.1 _ (hR.2.1 0)).2 ⟨0, rfl⟩
    simpa using h
  rcases hcov.eq_or_eq projStabilizer_le_normalizer le_top with h | h
  · exact h
  · exact absurd h normalizer_pa1_ne_top

theorem map_pa1_eq_pa2 [Finite k] [CharP k 2] (hk : ∃ m : ℕ, Nat.card k = 2 ^ m)
    (α : MulAut (projectiveSL 3 k))
    (hU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k)
    (hP : (projStabilizer (flagSpace 3 k 1)).map α.toMonoidHom ≠
      projStabilizer (flagSpace 3 k 1)) :
    (pa1 k).map α.toMonoidHom = pa2 k := by
  have hU' : (projUnitriangular 3 k).map α.symm.toMonoidHom = projUnitriangular 3 k := by
    conv_lhs => rw [← hU]
    exact map_symm_map α _
  have key : ∀ β : MulAut (projectiveSL 3 k),
      (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k →
      ∀ X : Subgroup (projectiveSL 3 k), X ≤ projUnitriangular 3 k → (∀ x ∈ X, x * x = 1) →
        X.map β.toMonoidHom ≤ pa1 k ∨ X.map β.toMonoidHom ≤ pa2 k := by
    intro β hβ X hX h2
    refine le_or_le_proj (hβ ▸ Subgroup.map_mono hX) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h2 x hx, map_one]
  have h1s : ∀ x ∈ pa1 k, x * x = 1 := fun x hx => mul_self_of_mem_pa1 hx
  have h2s : ∀ x ∈ pa2 k, x * x = 1 := fun x hx => mul_self_of_mem_pa2 hx
  have hfix : (pa1 k).map α.toMonoidHom ≠ pa1 k := by
    intro h
    apply hP
    rw [← normalizer_pa1_eq hk, Subgroup.map_equiv_normalizer_eq, h]
  rcases key α hU _ pa1_le h1s with h1 | h1
  · exfalso
    rcases key α.symm hU' _ pa1_le h1s with h3 | h3
    · refine hfix (le_antisymm h1 fun x hx => ⟨α.symm x, h3 ⟨x, hx, rfl⟩, by simp⟩)
    · refine (not_pa1_le_pa2 (k := k)) fun x hx => ?_
      have h4 := h3 ⟨α x, h1 ⟨x, hx, rfl⟩, rfl⟩
      simpa using h4
  · rcases key α.symm hU' _ pa2_le h2s with h3 | h3
    · exact le_antisymm h1 fun y hy => ⟨α.symm y, h3 ⟨y, hy, rfl⟩, by simp⟩
    · exfalso
      refine (not_pa1_le_pa2 (k := k)) fun x hx => ?_
      have h4 := h3 ⟨α x, h1 ⟨x, hx, rfl⟩, rfl⟩
      simpa using h4

end CFSG.Quasithin.Ch3E213M.P5
