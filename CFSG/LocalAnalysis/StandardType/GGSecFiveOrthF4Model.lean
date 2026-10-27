module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.GroupTheory.Coxeter.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant
public import TauCeti.LinearAlgebra.QuadraticForm.Quaternary.Basic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl

public section

namespace CFSG.StandardType.OrthF3

open TauCeti
open Matrix

@[expose] def f4ModelForm : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) :=
  QuadraticMap.weightedSumSquares (ZMod 3) (fun _ => (1 : ZMod 3))

private def ct_om_A0 : Fin 4 → ZMod 3 := ![0,1,2,0]
private def ct_om_A1 : Fin 4 → ZMod 3 := ![0,0,1,2]
private def ct_om_A2 : Fin 4 → ZMod 3 := ![0,0,0,1]
private def ct_om_A3 : Fin 4 → ZMod 3 := ![2,1,1,1]

@[instance_reducible] private def ct_om_Inst0 : Invertible (f4ModelForm ct_om_A0) := ⟨2, by decide, by decide⟩
@[instance_reducible] private def ct_om_Inst1 : Invertible (f4ModelForm ct_om_A1) := ⟨2, by decide, by decide⟩
@[instance_reducible] private def ct_om_Inst2 : Invertible (f4ModelForm ct_om_A2) := ⟨1, by decide, by decide⟩
@[instance_reducible] private def ct_om_Inst3 : Invertible (f4ModelForm ct_om_A3) := ⟨1, by decide, by decide⟩

private noncomputable def ct_om_Refl0 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @QuadraticMap.reflection (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm ct_om_A0 ct_om_Inst0
private noncomputable def ct_om_Refl1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @QuadraticMap.reflection (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm ct_om_A1 ct_om_Inst1
private noncomputable def ct_om_Refl2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @QuadraticMap.reflection (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm ct_om_A2 ct_om_Inst2
private noncomputable def ct_om_Refl3 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @QuadraticMap.reflection (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm ct_om_A3 ct_om_Inst3

private noncomputable def ct_om_S0 : QuadraticMap.orthogonalGroup f4ModelForm :=
  ⟨ct_om_Refl0, @QuadraticMap.reflection_mem_orthogonalGroup (ZMod 3) (Fin 4 → ZMod 3) _ _ _
    f4ModelForm ct_om_A0 ct_om_Inst0⟩
private noncomputable def ct_om_S1 : QuadraticMap.orthogonalGroup f4ModelForm :=
  ⟨ct_om_Refl1, @QuadraticMap.reflection_mem_orthogonalGroup (ZMod 3) (Fin 4 → ZMod 3) _ _ _
    f4ModelForm ct_om_A1 ct_om_Inst1⟩
private noncomputable def ct_om_S2 : QuadraticMap.orthogonalGroup f4ModelForm :=
  ⟨ct_om_Refl2, @QuadraticMap.reflection_mem_orthogonalGroup (ZMod 3) (Fin 4 → ZMod 3) _ _ _
    f4ModelForm ct_om_A2 ct_om_Inst2⟩
private noncomputable def ct_om_S3 : QuadraticMap.orthogonalGroup f4ModelForm :=
  ⟨ct_om_Refl3, @QuadraticMap.reflection_mem_orthogonalGroup (ZMod 3) (Fin 4 → ZMod 3) _ _ _
    f4ModelForm ct_om_A3 ct_om_Inst3⟩

private def ct_om_A : Fin 4 → (Fin 4 → ZMod 3) := ![ct_om_A0, ct_om_A1, ct_om_A2, ct_om_A3]

@[instance_reducible] private def ct_om_Inst : (i : Fin 4) → Invertible (f4ModelForm (ct_om_A i))
  | ⟨0, _⟩ => ct_om_Inst0
  | ⟨1, _⟩ => ct_om_Inst1
  | ⟨2, _⟩ => ct_om_Inst2
  | ⟨3, _⟩ => ct_om_Inst3
private noncomputable def ct_om_Refl : (i : Fin 4) → (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  ![ct_om_Refl0, ct_om_Refl1, ct_om_Refl2, ct_om_Refl3]
private noncomputable def ct_om_S : Fin 4 → QuadraticMap.orthogonalGroup f4ModelForm :=
  ![ct_om_S0, ct_om_S1, ct_om_S2, ct_om_S3]

private def ct_om_M0 : Matrix (Fin 4) (Fin 4) (ZMod 3) := !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1]
private def ct_om_M1 : Matrix (Fin 4) (Fin 4) (ZMod 3) := !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]
private def ct_om_M2 : Matrix (Fin 4) (Fin 4) (ZMod 3) := !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,2]
private def ct_om_M3 : Matrix (Fin 4) (Fin 4) (ZMod 3) := !![2,2,2,2; 2,2,1,1; 2,1,2,1; 2,1,1,2]
private def ct_om_M : (i : Fin 4) → Matrix (Fin 4) (Fin 4) (ZMod 3) := ![ct_om_M0, ct_om_M1, ct_om_M2, ct_om_M3]

private theorem ct_om_S_coe (i : Fin 4) : (ct_om_S i : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) = ct_om_Refl i := by
  fin_cases i <;> rfl

private theorem ct_om_Refl0_apply (x : Fin 4 → ZMod 3) :
    ct_om_Refl0 x = x - (2 * QuadraticMap.polar f4ModelForm ct_om_A0 x) • ct_om_A0 := by
  unfold ct_om_Refl0; rw [QuadraticMap.reflection_apply]; rfl
private theorem ct_om_Refl1_apply (x : Fin 4 → ZMod 3) :
    ct_om_Refl1 x = x - (2 * QuadraticMap.polar f4ModelForm ct_om_A1 x) • ct_om_A1 := by
  unfold ct_om_Refl1; rw [QuadraticMap.reflection_apply]; rfl
private theorem ct_om_Refl2_apply (x : Fin 4 → ZMod 3) :
    ct_om_Refl2 x = x - (1 * QuadraticMap.polar f4ModelForm ct_om_A2 x) • ct_om_A2 := by
  unfold ct_om_Refl2; rw [QuadraticMap.reflection_apply]; rfl
private theorem ct_om_Refl3_apply (x : Fin 4 → ZMod 3) :
    ct_om_Refl3 x = x - (1 * QuadraticMap.polar f4ModelForm ct_om_A3 x) • ct_om_A3 := by
  unfold ct_om_Refl3; rw [QuadraticMap.reflection_apply]; rfl

private theorem ct_om_Sq (z : Fin 4 → ZMod 3) :
    f4ModelForm z = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := by
  revert z; decide

private theorem ct_om_Polar (x y : Fin 4 → ZMod 3) :
    QuadraticMap.polar f4ModelForm x y =
      2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3) := by
  rw [QuadraticMap.polar, ct_om_Sq (x + y), ct_om_Sq x, ct_om_Sq y]
  simp only [Pi.add_apply]
  ring

private theorem ct_om_Refl0_toMatrix :
    LinearMap.toMatrix' (ct_om_Refl0 : Module.End (ZMod 3) (Fin 4 → ZMod 3)) = ct_om_M0 := by
  ext j k
  rw [LinearMap.toMatrix'_apply]
  change ct_om_Refl0 (Pi.single k 1) j = ct_om_M0 j k
  rw [ct_om_Refl0_apply, ct_om_Polar]
  fin_cases j <;> fin_cases k <;>
    simp only [ct_om_A0, ct_om_M0, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  all_goals decide

private theorem ct_om_Refl1_toMatrix :
    LinearMap.toMatrix' (ct_om_Refl1 : Module.End (ZMod 3) (Fin 4 → ZMod 3)) = ct_om_M1 := by
  ext j k
  rw [LinearMap.toMatrix'_apply]
  change ct_om_Refl1 (Pi.single k 1) j = ct_om_M1 j k
  rw [ct_om_Refl1_apply, ct_om_Polar]
  fin_cases j <;> fin_cases k <;>
    simp only [ct_om_A1, ct_om_M1, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  all_goals decide

private theorem ct_om_Refl2_toMatrix :
    LinearMap.toMatrix' (ct_om_Refl2 : Module.End (ZMod 3) (Fin 4 → ZMod 3)) = ct_om_M2 := by
  ext j k
  rw [LinearMap.toMatrix'_apply]
  change ct_om_Refl2 (Pi.single k 1) j = ct_om_M2 j k
  rw [ct_om_Refl2_apply, ct_om_Polar]
  fin_cases j <;> fin_cases k <;>
    simp only [ct_om_A2, ct_om_M2, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  all_goals decide

private theorem ct_om_Refl3_toMatrix :
    LinearMap.toMatrix' (ct_om_Refl3 : Module.End (ZMod 3) (Fin 4 → ZMod 3)) = ct_om_M3 := by
  ext j k
  rw [LinearMap.toMatrix'_apply]
  change ct_om_Refl3 (Pi.single k 1) j = ct_om_M3 j k
  rw [ct_om_Refl3_apply, ct_om_Polar]
  fin_cases j <;> fin_cases k <;>
    simp only [ct_om_A3, ct_om_M3, Pi.single_apply, Pi.sub_apply, Pi.smul_apply]
  all_goals decide

private theorem ct_om_Refl_matrix (i : Fin 4) :
    (ct_om_Refl i : Module.End (ZMod 3) (Fin 4 → ZMod 3)) = Matrix.toLin' (ct_om_M i) := by
  rw [← Matrix.toLin'_toMatrix' (ct_om_Refl i : Module.End (ZMod 3) (Fin 4 → ZMod 3))]
  congr 1
  fin_cases i
  · exact ct_om_Refl0_toMatrix
  · exact ct_om_Refl1_toMatrix
  · exact ct_om_Refl2_toMatrix
  · exact ct_om_Refl3_toMatrix

private theorem ct_om_M_pow (i j : Fin 4) :
    (ct_om_M i * ct_om_M j) ^ (CoxeterMatrix.F₄ i j) = 1 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ct_om_Refl_pow (i j : Fin 4) :
    (ct_om_Refl i * ct_om_Refl j) ^ (CoxeterMatrix.F₄ i j) = 1 := by
  apply LinearEquiv.toLinearMap_injective
  have hcoe : ∀ (e : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) (n : ℕ),
      (↑(e ^ n) : Module.End (ZMod 3) (Fin 4 → ZMod 3)) =
        (↑e : Module.End (ZMod 3) (Fin 4 → ZMod 3)) ^ n := by
    intro e n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  rw [hcoe, LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_one,
    ct_om_Refl_matrix i, ct_om_Refl_matrix j]
  have hprod : Matrix.toLin' (ct_om_M i) * Matrix.toLin' (ct_om_M j) =
      Matrix.toLin' (ct_om_M i * ct_om_M j) := by
    rw [Matrix.toLin'_mul, Module.End.mul_eq_comp]
  rw [hprod, ← Matrix.toLin'_pow, ct_om_M_pow i j, Matrix.toLin'_one]

private theorem ct_om_S_pow (i j : Fin 4) :
    (ct_om_S i * ct_om_S j) ^ (CoxeterMatrix.F₄ i j) = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, ct_om_S_coe]
  exact ct_om_Refl_pow i j

private theorem ct_om_Liftable : (CoxeterMatrix.F₄).IsLiftable ct_om_S := fun i j => ct_om_S_pow i j

private noncomputable def ct_om_Phi :
    (CoxeterMatrix.F₄).Group →* QuadraticMap.orthogonalGroup f4ModelForm :=
  (CoxeterMatrix.F₄).toCoxeterSystem.lift ⟨ct_om_S, ct_om_Liftable⟩

private theorem ct_om_Phi_simple (i : Fin 4) :
    ct_om_Phi ((CoxeterMatrix.F₄).simple i) = ct_om_S i :=
  (CoxeterMatrix.F₄).toCoxeterSystem.lift_apply_simple ct_om_Liftable i

private theorem ct_om_A_ne_zero (i : Fin 4) : f4ModelForm (ct_om_A i) ≠ 0 := by
  fin_cases i <;> decide

private theorem ct_om_OrthRefl (i : Fin 4) :
    OrthReflOfNorm f4ModelForm (f4ModelForm (ct_om_A i))
      ((ct_om_S i : QuadraticMap.orthogonalGroup f4ModelForm) :
        (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) := by
  refine ⟨ct_om_A i, ct_om_Inst i, rfl, ?_⟩
  rw [QuadraticMap.coe_reflectionOrthogonal, ct_om_S_coe i]
  fin_cases i <;> rfl

@[instance_reducible] private def ct_om_I2 : Invertible (2 : ZMod 3) := ⟨2, by decide, by decide⟩

private theorem ct_om_Nondeg : f4ModelForm.Nondegenerate := by
  have : Invertible (2 : ZMod 3) := ct_om_I2
  exact QuadraticMap.nondegenerate_weightedSumSquares (fun _ => isRegular_one)

private def ct_om_Act (i : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  Matrix.toLin' (ct_om_M i) v

private def ct_om_Roots : Finset (Fin 4 → ZMod 3) := {ct_om_A 0, ct_om_A 1, ct_om_A 2, ct_om_A 3}

private def ct_om_Step (S : Finset (Fin 4 → ZMod 3)) : Finset (Fin 4 → ZMod 3) :=
  S ∪ (S.product Finset.univ).image (fun p : (Fin 4 → ZMod 3) × Fin 4 => ct_om_Act p.2 p.1)

@[irreducible] private def ct_om_Orbit : Finset (Fin 4 → ZMod 3) := ct_om_Step^[8] ct_om_Roots

private theorem ct_om_orbit_complete :
    ∀ v : Fin 4 → ZMod 3, f4ModelForm v ≠ 0 → v ∈ ct_om_Orbit := by
  decide +kernel

private def ct_om_Good (v : Fin 4 → ZMod 3) : Prop :=
  f4ModelForm v ≠ 0 ∧
    ∀ (h : Invertible (f4ModelForm v)),
      @QuadraticMap.reflectionOrthogonal (ZMod 3) (Fin 4 → ZMod 3) _ _ _
        f4ModelForm v h ∈ ct_om_Phi.range

private theorem ct_om_Act_eq (i : Fin 4) (w : Fin 4 → ZMod 3) :
    ct_om_Act i w = (ct_om_S i : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) w := by
  rw [ct_om_S_coe i]
  change Matrix.toLin' (ct_om_M i) w = (ct_om_Refl i : Module.End (ZMod 3) (Fin 4 → ZMod 3)) w
  rw [ct_om_Refl_matrix i]

private theorem ct_om_ReflOrtho_congr {v v' : Fin 4 → ZMod 3} (hv : v = v')
    (h : Invertible (f4ModelForm v)) (h' : Invertible (f4ModelForm v')) :
    @QuadraticMap.reflectionOrthogonal (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm v h =
      @QuadraticMap.reflectionOrthogonal (ZMod 3) (Fin 4 → ZMod 3) _ _ _ f4ModelForm v' h' := by
  subst hv
  congr 1
  exact Subsingleton.elim _ _

private theorem ct_om_A_good0 : ct_om_Good ct_om_A0 := by
  refine ⟨by decide, fun h => ?_⟩
  have hh : h = ct_om_Inst0 := Subsingleton.elim h ct_om_Inst0
  rw [hh]
  refine MonoidHom.mem_range.mpr ⟨(CoxeterMatrix.F₄).simple 0, ?_⟩
  rw [ct_om_Phi_simple 0]
  apply Subtype.ext
  rw [QuadraticMap.coe_reflectionOrthogonal, ct_om_S_coe 0]
  rfl

private theorem ct_om_A_good1 : ct_om_Good ct_om_A1 := by
  refine ⟨by decide, fun h => ?_⟩
  have hh : h = ct_om_Inst1 := Subsingleton.elim h ct_om_Inst1
  rw [hh]
  refine MonoidHom.mem_range.mpr ⟨(CoxeterMatrix.F₄).simple 1, ?_⟩
  rw [ct_om_Phi_simple 1]
  apply Subtype.ext
  rw [QuadraticMap.coe_reflectionOrthogonal, ct_om_S_coe 1]
  rfl

private theorem ct_om_A_good2 : ct_om_Good ct_om_A2 := by
  refine ⟨by decide, fun h => ?_⟩
  have hh : h = ct_om_Inst2 := Subsingleton.elim h ct_om_Inst2
  rw [hh]
  refine MonoidHom.mem_range.mpr ⟨(CoxeterMatrix.F₄).simple 2, ?_⟩
  rw [ct_om_Phi_simple 2]
  apply Subtype.ext
  rw [QuadraticMap.coe_reflectionOrthogonal, ct_om_S_coe 2]
  rfl

private theorem ct_om_A_good3 : ct_om_Good ct_om_A3 := by
  refine ⟨by decide, fun h => ?_⟩
  have hh : h = ct_om_Inst3 := Subsingleton.elim h ct_om_Inst3
  rw [hh]
  refine MonoidHom.mem_range.mpr ⟨(CoxeterMatrix.F₄).simple 3, ?_⟩
  rw [ct_om_Phi_simple 3]
  apply Subtype.ext
  rw [QuadraticMap.coe_reflectionOrthogonal, ct_om_S_coe 3]
  rfl

private theorem ct_om_Roots_good {v : Fin 4 → ZMod 3} (hv : v ∈ ct_om_Roots) : ct_om_Good v := by
  simp only [ct_om_Roots, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h
  · subst h; exact ct_om_A_good0
  · subst h; exact ct_om_A_good1
  · subst h; exact ct_om_A_good2
  · subst h; exact ct_om_A_good3

private theorem ct_om_Good_conj (i : Fin 4) {w : Fin 4 → ZMod 3} (hw : ct_om_Good w) :
    ct_om_Good (ct_om_Act i w) := by
  have hQ : f4ModelForm (ct_om_Act i w) = f4ModelForm w := by
    rw [ct_om_Act_eq i w]
    exact QuadraticMap.map_app_of_mem_orthogonalGroup (ct_om_S i).2 w
  refine ⟨fun hzero => hw.1 (hQ ▸ hzero), fun h' => ?_⟩
  let h : Invertible (f4ModelForm w) := (isUnit_iff_ne_zero.mpr hw.1).invertible
  have hsw : @QuadraticMap.reflectionOrthogonal (ZMod 3) (Fin 4 → ZMod 3) _ _ _
      f4ModelForm w h ∈ ct_om_Phi.range := hw.2 h
  let h'' : Invertible (f4ModelForm ((ct_om_S i : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) w)) := by
    rw [← ct_om_Act_eq i w]; exact h'
  have hconj := @QuadraticMap.mul_reflectionOrthogonal_mul_inv (ZMod 3) (Fin 4 → ZMod 3) _ _ _
      f4ModelForm (ct_om_S i) w h h''
  have hsi : ct_om_S i ∈ ct_om_Phi.range :=
    MonoidHom.mem_range.mpr ⟨(CoxeterMatrix.F₄).simple i, ct_om_Phi_simple i⟩
  have hmem : ct_om_S i * @QuadraticMap.reflectionOrthogonal (ZMod 3) (Fin 4 → ZMod 3) _ _ _
      f4ModelForm w h * (ct_om_S i)⁻¹ ∈ ct_om_Phi.range :=
    ct_om_Phi.range.mul_mem (ct_om_Phi.range.mul_mem hsi hsw) (ct_om_Phi.range.inv_mem hsi)
  rw [hconj] at hmem
  have heq := ct_om_ReflOrtho_congr (ct_om_Act_eq i w) h' h''
  rw [heq]
  exact hmem

private theorem ct_om_Step_good {S : Finset (Fin 4 → ZMod 3)}
    (hS : ∀ v ∈ S, ct_om_Good v) : ∀ v ∈ ct_om_Step S, ct_om_Good v := by
  intro v hv
  simp only [ct_om_Step, Finset.mem_union, Finset.mem_image, Prod.exists] at hv
  rcases hv with hv | ⟨w, i, hw, rfl⟩
  · exact hS v hv
  · exact ct_om_Good_conj i (hS w (Finset.mem_product.mp hw).1)

private theorem ct_om_Orbit_good : ∀ v ∈ ct_om_Orbit, ct_om_Good v := by
  unfold ct_om_Orbit
  have h : ∀ n, ∀ v ∈ ct_om_Step^[n] ct_om_Roots, ct_om_Good v := by
    intro n
    induction n with
    | zero => intro v hv; exact ct_om_Roots_good hv
    | succ n ih =>
      intro v hv
      exact ct_om_Step_good ih v (by simpa only [Function.iterate_succ_apply'] using hv)
  simpa using h 8

theorem f4Model_hom :
    ∃ Φ : (CoxeterMatrix.F₄).Group →* QuadraticMap.orthogonalGroup f4ModelForm, Function.Surjective Φ ∧
      ∀ i : Fin 4, ∃ c : ZMod 3, c ≠ 0 ∧
        OrthReflOfNorm f4ModelForm c ((Φ ((CoxeterMatrix.F₄).simple i) : QuadraticMap.orthogonalGroup f4ModelForm) :
          (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) := by
  refine ⟨ct_om_Phi, ?_, ?_⟩
  · rw [← MonoidHom.range_eq_top]
    have : NeZero (2 : ZMod 3) := ⟨by decide⟩
    refine QuadraticMap.subgroup_eq_top_of_reflection_mem f4ModelForm ct_om_Nondeg ct_om_Phi.range ?_
    intro v hv
    have hvnz : f4ModelForm v ≠ 0 :=
      (@isUnit_of_invertible (ZMod 3) _ (f4ModelForm v) hv).ne_zero
    have hmem : v ∈ ct_om_Orbit := ct_om_orbit_complete v hvnz
    exact (ct_om_Orbit_good v hmem).2 hv
  · intro i
    refine ⟨f4ModelForm (ct_om_A i), ct_om_A_ne_zero i, ?_⟩
    rw [ct_om_Phi_simple i]
    exact ct_om_OrthRefl i

private theorem ct_om_pair {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    [FiniteDimensional (ZMod 3) W]
    (Q : QuadraticForm (ZMod 3) W) (U : Submodule (ZMod 3) W)
    (hU : Module.finrank (ZMod 3) U = 2) (hU0 : ∀ x ∈ U, Q x = 0) :
    ∃ u v : W, u ≠ 0 ∧ (∀ c : ZMod 3, v ≠ c • u) ∧ Q u = 0 ∧ Q v = 0 ∧
      QuadraticMap.polar Q u v = 0 := by
  classical
  let b : Module.Basis (Fin 2) (ZMod 3) U := (Module.finBasis (ZMod 3) U).reindex (finCongr hU)
  refine ⟨(b 0 : W), (b 1 : W), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact b.ne_zero 0 (Subtype.ext h)
  · intro c hc
    have hli : LinearIndependent (ZMod 3) ![(b 0 : U), (b 1 : U)] := by
      have hb_eq : (fun i : Fin 2 => b i) = ![b 0, b 1] := by
        funext i; fin_cases i <;> rfl
      rw [← hb_eq]
      exact b.linearIndependent
    have hb : (b 1 : U) = c • (b 0 : U) := Subtype.ext hc
    have hrel : (-c) • (b 0 : U) + (1 : ZMod 3) • (b 1 : U) = 0 := by
      rw [one_smul, hb, neg_smul]
      exact neg_add_cancel _
    exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) (-c) 1 hrel).2
  · exact hU0 (b 0) (b 0).2
  · exact hU0 (b 1) (b 1).2
  · rw [QuadraticMap.polar]
    rw [hU0 ((b 0 : U) + (b 1 : U)) (U.add_mem (b 0).2 (b 1).2),
      hU0 (b 0) (b 0).2, hU0 (b 1) (b 1).2]
    ring

private theorem ct_om_not_square_no_pair (w : Fin 4 → (ZMod 3)ˣ)
    (h : ¬ IsSquare (∏ i, w i)) :
    ¬ ∃ u v : Fin 4 → ZMod 3, u ≠ 0 ∧ (∀ c : ZMod 3, v ≠ c • u) ∧
      (QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))) u = 0 ∧
      (QuadraticMap.weightedSumSquares (ZMod 3) (fun i => (w i : ZMod 3))) v = 0 ∧
      QuadraticMap.polar (QuadraticMap.weightedSumSquares (ZMod 3)
        (fun i => (w i : ZMod 3))) u v = 0 := by
  revert w
  decide +kernel

theorem f4Model_isometric {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : Module.finrank (ZMod 3) V = 4)
    (hplus : ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ∃ e : V ≃ₗ[ZMod 3] (Fin 4 → ZMod 3), ∀ v, f4ModelForm (e v) = Q v := by
  classical
  have : Invertible (2 : ZMod 3) := ct_om_I2
  have : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos (by rw [hd]; norm_num)
  obtain ⟨W, hWrank, hW0⟩ := hplus
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hiso : ¬ Q.Anisotropic := by
    rw [QuadraticMap.not_anisotropic_iff_exists]
    have hpos : 0 < Module.finrank (ZMod 3) W := by rw [hWrank]; norm_num
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact ⟨(x : V), fun h => hx (Subtype.ext h), hW0 x x.2⟩
  have hassoc : (QuadraticMap.associated (R := ZMod 3) Q).SeparatingLeft :=
    ((QuadraticMap.nondegenerate_associated_iff (Q := Q)).mpr hQ').1
  obtain ⟨w, he⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hassoc
  let idx : Fin 4 ≃ Fin (Module.finrank (ZMod 3) V) := (finCongr hd).symm
  let w4 : Fin 4 → (ZMod 3)ˣ := w ∘ idx
  have he4 : Q.Equivalent (QuadraticMap.weightedSumSquares (ZMod 3) w4) :=
    he.trans ⟨QuadraticForm.isometryEquivWeightedSumSquaresReindex w idx⟩
  let e := he4.some
  let W' : Submodule (ZMod 3) (Fin 4 → ZMod 3) := W.map e.toLinearEquiv.toLinearMap
  have hW'rank : Module.finrank (ZMod 3) W' = 2 := by
    simpa only [W'] using (e.toLinearEquiv.finrank_map_eq W).trans hWrank
  have hW'0 : ∀ x ∈ W', QuadraticMap.weightedSumSquares (ZMod 3) w4 x = 0 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (QuadraticMap.weightedSumSquares (ZMod 3) w4) (e y) = 0
    rw [e.map_app]
    exact hW0 y hy
  obtain ⟨u, v, hu, hind, hu0, hv0, huv⟩ :=
    ct_om_pair (QuadraticMap.weightedSumSquares (ZMod 3) w4) W' hW'rank hW'0
  rw [QuadraticMap.weightedSumSquares_units] at hu0 hv0 huv
  have hsq : IsSquare (∏ i, w4 i) := by
    by_contra hnsq
    exact ct_om_not_square_no_pair w4 hnsq ⟨u, v, hu, hind, hu0, hv0, huv⟩
  have hdiscr : RegularFormClass.discr (formClass Q hQ') = 0 := by
    have hclass : formClass Q hQ' =
        Quotient.mk (regularFormSetoid (ZMod 3)) (⟨4, w4⟩ : RegularFormPresentation (ZMod 3)) :=
      formClass_mk Q hQ' ⟨4, w4⟩ (by rw [presentedForm_eq_weightedSumSquares]; exact he4)
    rw [hclass, RegularFormClass.discr_mk]
    exact (squareClass_eq_zero_iff (∏ i, w4 i)).mpr hsq
  obtain ⟨eQH⟩ := hQ'.equivalent_hyperbolicPlane_prod_self hd hdiscr hiso
  have hQ0 : f4ModelForm.Nondegenerate :=
    QuadraticMap.nondegenerate_weightedSumSquares (fun _ => isRegular_one)
  have hMH : f4ModelForm.Equivalent
      ((hyperbolicPlane (ZMod 3)).prod (hyperbolicPlane (ZMod 3))) := by
    refine hQ0.equivalent_hyperbolicPlane_prod_self (by simp) ?_ ?_
    · have hclass : formClass f4ModelForm hQ0 =
          Quotient.mk (regularFormSetoid (ZMod 3))
            (⟨4, fun _ => (1 : (ZMod 3)ˣ)⟩ : RegularFormPresentation (ZMod 3)) :=
        formClass_mk f4ModelForm hQ0 ⟨4, fun _ => 1⟩
          (by rw [presentedForm_eq_weightedSumSquares]; rfl)
      rw [hclass, RegularFormClass.discr_mk, Fin.prod_const]
      exact (squareClass_eq_zero_iff (1 : (ZMod 3)ˣ)).mpr IsSquare.one
    · rw [QuadraticMap.not_anisotropic_iff_exists]
      exact ⟨![1,1,1,0], by decide, by decide⟩
  obtain ⟨eMH⟩ := hMH
  exact ⟨(eQH.trans eMH.symm).toLinearEquiv, fun v => (eQH.trans eMH.symm).map_app v⟩

end CFSG.StandardType.OrthF3

end
