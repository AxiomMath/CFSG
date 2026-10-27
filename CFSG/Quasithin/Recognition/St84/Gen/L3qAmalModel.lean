module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDefs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA
import CFSG.GH74.QTGen4.DSGen4.L34Generic
import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieAbs

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin257.L3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.Quasithin.H13.F431.L3.P3
open CFSG.QuasithinUnique.Setup.X7a
open Matrix
open CFSG.GH74.QTGen4.DSGen4.L34

theorem isLieOverTwo_psl3 {f : ℕ} (hf : 2 ≤ f) :
    IsLieOverTwo .PSL 3 f (projectiveSL 3 (GaloisField 2 f)) := by
  refine (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).2 ?_
  refine ⟨⟨Nat.prime_two, by omega, by omega, by simp, by simp⟩, GaloisField 2 f, inferInstance,
    inferInstance, GaloisField.card 2 f (by omega), ⟨?_⟩⟩
  exact CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 (GaloisField 2 f)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isYAmalgamPair_L3 :
    IsYAmalgamPair (projUnitriangular 3 F) (Ln F) (Pt F) :=
  isYAmalgamPair_of_borelData
    (CFSG.Quasithin.H13.F431.L3.borelData_swap
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F)))
    (CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup (F := F))

private def v2Hom : Multiplicative (Fin 2 → F) →* ↥(V2 : Subgroup (projectiveSL 3 F)) where
  toFun v := ⟨yP (Multiplicative.toAdd v 1) * wP (Multiplicative.toAdd v 0),
    mem_V2.mpr ⟨_, _, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp [yP_zero, wP_zero]
  map_mul' v w := by
    apply Subtype.ext
    show yP (Multiplicative.toAdd (v * w) 1) * wP (Multiplicative.toAdd (v * w) 0) =
      (yP (Multiplicative.toAdd v 1) * wP (Multiplicative.toAdd v 0)) *
        (yP (Multiplicative.toAdd w 1) * wP (Multiplicative.toAdd w 0))
    rw [toAdd_mul]
    simp only [Pi.add_apply]
    rw [V2_mul]

private theorem v2Hom_injective : Function.Injective (v2Hom (F := F)) := by
  intro v w h
  have h' : yP (Multiplicative.toAdd v 1) * wP (Multiplicative.toAdd v 0) =
      yP (Multiplicative.toAdd w 1) * wP (Multiplicative.toAdd w 0) :=
    congrArg Subtype.val h
  obtain ⟨hb, hc⟩ := yP_wP_inj h'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [hb, hc]

private theorem v2Hom_surjective : Function.Surjective (v2Hom (F := F)) := by
  rintro ⟨g, hg⟩
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hg
  refine ⟨Multiplicative.ofAdd ![c, b], ?_⟩
  apply Subtype.ext
  simp [v2Hom]

private def v2Equiv : Multiplicative (Fin 2 → F) ≃* ↥(V2 : Subgroup (projectiveSL 3 F)) :=
  MulEquiv.ofBijective v2Hom ⟨v2Hom_injective, v2Hom_surjective⟩

private def vecV2 : ↥(V2 : Subgroup (projectiveSL 3 F)) ≃* Multiplicative (Fin 2 → F) :=
  (v2Equiv (F := F)).symm

private theorem vecV2_apply (b c : F) :
    vecV2 (⟨yP b * wP c, mem_V2.mpr ⟨b, c, rfl⟩⟩ :
      ↥(V2 : Subgroup (projectiveSL 3 F))) = Multiplicative.ofAdd ![c, b] := by
  refine (MulEquiv.symm_apply_eq (v2Equiv (F := F))).mpr ?_
  apply Subtype.ext
  simp [v2Equiv, v2Hom]

private def v1Hom : Multiplicative (Fin 2 → F) →* ↥(V1 : Subgroup (projectiveSL 3 F)) where
  toFun v := ⟨xP (Multiplicative.toAdd v 0) * wP (Multiplicative.toAdd v 1),
    mem_V1.mpr ⟨_, _, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp [xP_zero, wP_zero]
  map_mul' v w := by
    apply Subtype.ext
    show xP (Multiplicative.toAdd (v * w) 0) * wP (Multiplicative.toAdd (v * w) 1) =
      (xP (Multiplicative.toAdd v 0) * wP (Multiplicative.toAdd v 1)) *
        (xP (Multiplicative.toAdd w 0) * wP (Multiplicative.toAdd w 1))
    rw [toAdd_mul]
    simp only [Pi.add_apply]
    rw [V1_mul]

private theorem v1Hom_injective : Function.Injective (v1Hom (F := F)) := by
  intro v w h
  have h' : xP (Multiplicative.toAdd v 0) * wP (Multiplicative.toAdd v 1) =
      xP (Multiplicative.toAdd w 0) * wP (Multiplicative.toAdd w 1) :=
    congrArg Subtype.val h
  obtain ⟨ha, hc⟩ := xP_mul_wP_inj h'
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp [ha, hc]

private theorem v1Hom_surjective : Function.Surjective (v1Hom (F := F)) := by
  rintro ⟨g, hg⟩
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
  refine ⟨Multiplicative.ofAdd ![a, c], ?_⟩
  apply Subtype.ext
  simp [v1Hom]

private def v1Equiv : Multiplicative (Fin 2 → F) ≃* ↥(V1 : Subgroup (projectiveSL 3 F)) :=
  MulEquiv.ofBijective v1Hom ⟨v1Hom_injective, v1Hom_surjective⟩

private def vecV1 : ↥(V1 : Subgroup (projectiveSL 3 F)) ≃* Multiplicative (Fin 2 → F) :=
  (v1Equiv (F := F)).symm

private theorem vecV1_apply (a c : F) :
    vecV1 (⟨xP a * wP c, mem_V1.mpr ⟨a, c, rfl⟩⟩ :
      ↥(V1 : Subgroup (projectiveSL 3 F))) = Multiplicative.ofAdd ![a, c] := by
  refine (MulEquiv.symm_apply_eq (v1Equiv (F := F))).mpr ?_
  apply Subtype.ext
  simp [v1Equiv, v1Hom]

private theorem conj_yP_wP_Q3_one {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 1) (b c : F) :
    proj 3 F M * (yP b * wP c) * (proj 3 F M)⁻¹ =
      yP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 1 1 * b +
          (M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 1 0 * c) *
      wP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 0 1 * b +
          (M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 0 0 * c) := by
  have hy := conj_yP_Q3 hM b
  have hw := conj_wP_Q3' hM c
  calc proj 3 F M * (yP b * wP c) * (proj 3 F M)⁻¹
      = (proj 3 F M * yP b * (proj 3 F M)⁻¹) *
          (proj 3 F M * wP c * (proj 3 F M)⁻¹) := by group
    _ = (yP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 1 1 * b) *
          wP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 0 1 * b)) *
          (yP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 1 0 * c) *
          wP ((M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 0 0 * c)) := by
        rw [hy, hw]
    _ = _ := by rw [V2_mul]

private theorem conj_xP_wP_Q3_zero {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 0) (a c : F) :
    proj 3 F M * (xP a * wP c) * (proj 3 F M)⁻¹ =
      xP ((M.1 0 0) ^ 2 * M.1 2 2 * a + (M.1 0 0) ^ 2 * M.1 2 1 * c) *
      wP ((M.1 0 0) ^ 2 * M.1 1 2 * a + (M.1 0 0) ^ 2 * M.1 1 1 * c) := by
  have hx := conj_xP_Q3 hM a
  have hw := conj_wP_Q3 hM c
  calc proj 3 F M * (xP a * wP c) * (proj 3 F M)⁻¹
      = (proj 3 F M * xP a * (proj 3 F M)⁻¹) *
          (proj 3 F M * wP c * (proj 3 F M)⁻¹) := by group
    _ = (xP ((M.1 0 0) ^ 2 * M.1 2 2 * a) *
          wP ((M.1 0 0) ^ 2 * M.1 1 2 * a)) *
          (xP ((M.1 0 0) ^ 2 * M.1 2 1 * c) *
          wP ((M.1 0 0) ^ 2 * M.1 1 1 * c)) := by
        rw [hx, hw]
    _ = _ := by rw [V1_mul]

private def blk2SL (A : GL (Fin 2) F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
     (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
     0, 0, ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹], by
    have hA : ((A : Matrix (Fin 2) (Fin 2) F)).det =
        ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) := rfl
    have hd : ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) *
        ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ = 1 :=
      mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det A).ne_zero
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, Matrix.zero_apply, mul_zero, sub_zero, mul_one,
      zero_mul, sub_self, add_zero]
    rw [← hA, Matrix.det_fin_two] at hd
    rw [← hA, Matrix.det_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
    linear_combination hd⟩

private def blk1SL (A : GL (Fin 2) F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹, 0, 0;
     0, (A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1;
     0, (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1], by
    have hA : ((A : Matrix (Fin 2) (Fin 2) F)).det =
        ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) := rfl
    have hd : ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) *
        ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ = 1 :=
      mul_inv_cancel₀ (Matrix.GeneralLinearGroup.det A).ne_zero
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, Matrix.zero_apply, mul_zero, sub_zero, mul_one,
      zero_mul, sub_self, add_zero]
    rw [← hA, Matrix.det_fin_two] at hd
    rw [← hA, Matrix.det_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
    linear_combination hd⟩

private def blk2Hom : GL (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun := blk2SL
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk2SL]
  map_mul' A B := by
    apply Subtype.ext
    show ((blk2SL (A * B) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((blk2SL A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((blk2SL B : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk2SL, Matrix.mul_apply, Fin.sum_univ_three, map_mul, mul_inv] <;> ring

private def blk1Hom : GL (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun := blk1SL
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk1SL]
  map_mul' A B := by
    apply Subtype.ext
    show ((blk1SL (A * B) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((blk1SL A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((blk1SL B : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk1SL, Matrix.mul_apply, Fin.sum_univ_three, map_mul, mul_inv] <;> ring

private def lev2Hom : GL (Fin 2) F →* projectiveSL 3 F :=
  (proj 3 F).comp blk2Hom

private def lev1Hom : GL (Fin 2) F →* projectiveSL 3 F :=
  (proj 3 F).comp blk1Hom

private def q1Delta (M : Matrix.SpecialLinearGroup (Fin 3) F) : F :=
  M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0

private theorem q1Delta_ne_zero {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 1) :
    q1Delta M ≠ 0 := by
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hd := det_V2 h20 h21
  intro h
  have hd' : M.1 2 2 * q1Delta M = 1 := hd
  rw [h] at hd'
  have h01 : (0 : F) = 1 := by simpa using hd'
  exact zero_ne_one h01

private def q1ActionMat (M : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![q1Delta M * M.1 0 0, q1Delta M * M.1 0 1;
     q1Delta M * M.1 1 0, q1Delta M * M.1 1 1]

private theorem det_q1ActionMat (M : Matrix.SpecialLinearGroup (Fin 3) F) :
    (q1ActionMat M).det = q1Delta M ^ 3 := by
  simp only [q1ActionMat, q1Delta, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons]
  ring

private def q1ActionGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 1) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (q1ActionMat M) (by
    rw [det_q1ActionMat]
    exact pow_ne_zero 3 (q1Delta_ne_zero hM))

private theorem det_q1ActionGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 1) :
    Matrix.GeneralLinearGroup.det (q1ActionGL M hM) =
      (Units.mk0 (q1Delta M) (q1Delta_ne_zero hM)) ^ 3 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (q1ActionMat M).det = q1Delta M ^ 3
  exact det_q1ActionMat M

private theorem q1ActionGL_mem (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 1) : q1ActionGL M hM ∈ cubeDetGL F := by
  rw [cubeDetGL, Subgroup.mem_comap, MonoidHom.mem_range]
  exact ⟨Units.mk0 (q1Delta M) (q1Delta_ne_zero hM), (det_q1ActionGL M hM).symm⟩

private theorem actsByMatrix_q1_mat {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 1) :
    ActsByMatrix vecV2 (proj 3 F M) (q1ActionMat M) := by
  intro x y hy
  obtain ⟨b, c, hxval⟩ := mem_V2.mp x.2
  have hx : x = ⟨yP b * wP c, mem_V2.mpr ⟨b, c, rfl⟩⟩ := Subtype.ext hxval
  have hyval : (y : projectiveSL 3 F) =
      proj 3 F M * (yP b * wP c) * (proj 3 F M)⁻¹ := by
    rw [hy, hx]
  set b' : F := q1Delta M * M.1 1 1 * b + q1Delta M * M.1 1 0 * c with hb'
  set c' : F := q1Delta M * M.1 0 1 * b + q1Delta M * M.1 0 0 * c with hc'
  have hyeq : y = ⟨yP b' * wP c', mem_V2.mpr ⟨b', c', rfl⟩⟩ := by
    apply Subtype.ext
    rw [hyval, conj_yP_wP_Q3_one hM b c]
    simp only [Subtype.coe_mk, q1Delta, hb', hc']
  rw [hx, hyeq, vecV2_apply, vecV2_apply]
  change ![c', b'] = q1ActionMat M *ᵥ ![c, b]
  funext i
  fin_cases i <;>
    simp [q1ActionMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hb', hc']
  all_goals ring

private theorem actsByMatrix_q1 {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 1) :
    ActsByMatrix vecV2 (proj 3 F M)
      (q1ActionGL M hM : Matrix (Fin 2) (Fin 2) F) :=
  actsByMatrix_q1_mat hM

private def q0Delta (M : Matrix.SpecialLinearGroup (Fin 3) F) : F :=
  M.1 0 0

private theorem q0Delta_ne_zero {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 0) :
    q0Delta M ≠ 0 := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hd := det_V1 h10 h20
  intro h
  have hd' : q0Delta M * (M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1) = 1 := hd
  rw [h] at hd'
  have h01 : (0 : F) = 1 := by simpa using hd'
  exact zero_ne_one h01

private def q0ActionMat (M : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  !![q0Delta M ^ 2 * M.1 2 2, q0Delta M ^ 2 * M.1 2 1;
     q0Delta M ^ 2 * M.1 1 2, q0Delta M ^ 2 * M.1 1 1]

private theorem det_q0ActionMat {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 0) : (q0ActionMat M).det = q0Delta M ^ 3 := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hd := det_V1 h10 h20
  simp only [q0ActionMat, q0Delta, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (M.1 0 0 ^ 3) * hd

private def q0ActionGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (q0ActionMat M) (by
    rw [det_q0ActionMat hM]
    exact pow_ne_zero 3 (q0Delta_ne_zero hM))

private theorem det_q0ActionGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 0) :
    Matrix.GeneralLinearGroup.det (q0ActionGL M hM) =
      (Units.mk0 (q0Delta M) (q0Delta_ne_zero hM)) ^ 3 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change (q0ActionMat M).det = q0Delta M ^ 3
  exact det_q0ActionMat hM

private theorem q0ActionGL_mem (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 0) : q0ActionGL M hM ∈ cubeDetGL F := by
  rw [cubeDetGL, Subgroup.mem_comap, MonoidHom.mem_range]
  exact ⟨Units.mk0 (q0Delta M) (q0Delta_ne_zero hM), (det_q0ActionGL M hM).symm⟩

private theorem actsByMatrix_q0_mat {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 0) :
    ActsByMatrix vecV1 (proj 3 F M) (q0ActionMat M) := by
  intro x y hy
  obtain ⟨a, c, hxval⟩ := mem_V1.mp x.2
  have hx : x = ⟨xP a * wP c, mem_V1.mpr ⟨a, c, rfl⟩⟩ := Subtype.ext hxval
  have hyval : (y : projectiveSL 3 F) =
      proj 3 F M * (xP a * wP c) * (proj 3 F M)⁻¹ := by
    rw [hy, hx]
  set a' : F := q0Delta M ^ 2 * M.1 2 2 * a + q0Delta M ^ 2 * M.1 2 1 * c with ha'
  set c' : F := q0Delta M ^ 2 * M.1 1 2 * a + q0Delta M ^ 2 * M.1 1 1 * c with hc'
  have hyeq : y = ⟨xP a' * wP c', mem_V1.mpr ⟨a', c', rfl⟩⟩ := by
    apply Subtype.ext
    rw [hyval, conj_xP_wP_Q3_zero hM a c]
    simp only [Subtype.coe_mk, q0Delta, ha', hc']
  rw [hx, hyeq, vecV1_apply, vecV1_apply]
  change ![a', c'] = q0ActionMat M *ᵥ ![a, c]
  funext i
  fin_cases i <;>
    simp [q0ActionMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha', hc']
  all_goals ring

private theorem actsByMatrix_q0 {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 0) :
    ActsByMatrix vecV1 (proj 3 F M)
      (q0ActionGL M hM : Matrix (Fin 2) (Fin 2) F) :=
  actsByMatrix_q0_mat hM

private def q1BlockGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 1) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1] (by
      rw [Matrix.det_fin_two]
      exact q1Delta_ne_zero hM)

private theorem det_q1BlockGL {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 1) :
    ((Matrix.GeneralLinearGroup.det (q1BlockGL M hM) : Fˣ) : F) = q1Delta M := by
  change (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1] : Matrix (Fin 2) (Fin 2) F).det = q1Delta M
  rw [Matrix.det_fin_two]
  rfl

private theorem q1_bottom_right {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 1) : M.1 2 2 = (q1Delta M)⁻¹ := by
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hd := det_V2 h20 h21
  have hd' : q1Delta M * M.1 2 2 = 1 := by rw [mul_comm]; exact hd
  exact eq_inv_of_mul_eq_one_right hd'

private theorem q1Delta_blk2SL (A : GL (Fin 2) F) :
    q1Delta (blk2SL A) = ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) := by
  simp [q1Delta, blk2SL, Matrix.det_fin_two]

private theorem q1ActionMat_blk2SL (A : GL (Fin 2) F) :
    q1ActionMat (blk2SL A) =
      ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) • (A : Matrix (Fin 2) (Fin 2) F) := by
  simp only [q1ActionMat]
  rw [q1Delta_blk2SL A]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2SL, Matrix.smul_apply]

private theorem coe_blk2SL (A : GL (Fin 2) F) :
    ((blk2SL A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
        (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0;
        0, 0, ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹] := rfl

private theorem coe_yMat_mul_wMat (b c : F) :
    ((yMat b * wMat c : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = yM b * wM c := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  rfl

private theorem q1_decomp {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 1) :
    M = yMat (M.1 1 2 * q1Delta M) * wMat (M.1 0 2 * q1Delta M) *
      blk2SL (q1BlockGL M hM) := by
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hΔ0 := q1Delta_ne_zero hM
  have h22 := q1_bottom_right hM
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_yMat_mul_wMat, coe_blk2SL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q1BlockGL, det_q1BlockGL hM, h22, h20, h21, yM, wM,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals simp only [q1Delta] at hΔ0 ⊢
  all_goals field_simp [hΔ0]

private def unit1Mat (a c : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨xM a * wM c, by
    rw [Matrix.det_mul]
    simp [xM, wM, Matrix.det_fin_three]⟩

private theorem unit1Mat_eq (a c : F) :
    unit1Mat a c = xMat a * wMat c :=
  Subtype.ext rfl

private theorem proj_unit1Mat (a c : F) :
    proj 3 F (unit1Mat a c) = xP a * wP c := by
  rw [unit1Mat_eq, map_mul]
  rfl

private theorem coe_unit1Mat (a c : F) :
    ((unit1Mat a c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      xM a * wM c := rfl

private def q0BlockGL (M : Matrix.SpecialLinearGroup (Fin 3) F)
    (hM : M ∈ Q3 F 0) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![M.1 1 1, M.1 1 2; M.1 2 1, M.1 2 2] (by
      obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
      have hd := det_V1 h10 h20
      have hdet : M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1 = (q0Delta M)⁻¹ := by
        have hd' : q0Delta M * (M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1) = 1 := hd
        exact eq_inv_of_mul_eq_one_right hd'
      simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
      rw [hdet]
      exact inv_ne_zero (q0Delta_ne_zero hM))

private theorem det_q0BlockGL {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (hM : M ∈ Q3 F 0) :
    ((Matrix.GeneralLinearGroup.det (q0BlockGL M hM) : Fˣ) : F) = (q0Delta M)⁻¹ := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hd := det_V1 h10 h20
  have hdet : M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1 = (q0Delta M)⁻¹ := by
    have hd' : q0Delta M * (M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1) = 1 := hd
    exact eq_inv_of_mul_eq_one_right hd'
  change (!![M.1 1 1, M.1 1 2; M.1 2 1, M.1 2 2] : Matrix (Fin 2) (Fin 2) F).det =
    (q0Delta M)⁻¹
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  exact hdet

private theorem coe_blk1SL (A : GL (Fin 2) F) :
    ((blk1SL A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹, 0, 0;
        0, (A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1;
        0, (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl

private def swapMat {F : Type} [Field F] (X : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![X 1 1, X 1 0; X 0 1, X 0 0]

private theorem swapMat_swapMat {F : Type} [Field F] (X : Matrix (Fin 2) (Fin 2) F) :
    swapMat (swapMat X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat]

private theorem swapMat_smul {F : Type} [Field F] (c : F) (X : Matrix (Fin 2) (Fin 2) F) :
    swapMat (c • X) = c • swapMat X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.smul_apply]

private theorem swapMat_det {F : Type} [Field F] (X : Matrix (Fin 2) (Fin 2) F) :
    (swapMat X).det = X.det := by
  simp only [swapMat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem q0ActionMat_blk1SL (A : GL (Fin 2) F) :
    q0ActionMat (blk1SL A) =
      (((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹) ^ 2 •
        swapMat (A : Matrix (Fin 2) (Fin 2) F) := by
  simp only [q0ActionMat, q0Delta, blk1SL, swapMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

private theorem q0_decomp {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 0) :
    M = blk1SL (q0BlockGL M hM) *
      unit1Mat (M.1 0 1 * (q0Delta M)⁻¹) (M.1 0 2 * (q0Delta M)⁻¹) := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hΔ0 := q0Delta_ne_zero hM
  have hprod : M.1 0 0 * (M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1) = 1 :=
    det_V1 h10 h20
  have h00 : (q0Delta M)⁻¹ = M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1 := by
    exact (eq_inv_of_mul_eq_one_right hprod).symm
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_blk1SL, coe_unit1Mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q0BlockGL, det_q0BlockGL hM, h00, h10, h20, xM, wM,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals
    have hM00 : M.1 0 0 ≠ 0 := hΔ0
    have hB0 : M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1 ≠ 0 := by
      intro hB
      rw [hB, mul_zero] at hprod
      exact zero_ne_one hprod
    field_simp [hB0, hM00]
    try exact hprod

private theorem range_lev2_le_Ln : (lev2Hom (F := F)).range ≤ Ln F := by
  rintro _ ⟨A, rfl⟩
  rw [Ln, normalizer_V2_eq]
  refine ⟨blk2SL A, ?_, rfl⟩
  exact mem_Q3_one_iff.mpr ⟨by simp [blk2SL], by simp [blk2SL]⟩

private theorem range_lev1_le_Pt : (lev1Hom (F := F)).range ≤ Pt F := by
  rintro _ ⟨A, rfl⟩
  rw [Pt, normalizer_V1_eq]
  refine ⟨blk1SL A, ?_, rfl⟩
  exact mem_Q3_zero_iff.mpr ⟨by simp [blk1SL], by simp [blk1SL]⟩

private theorem V2_sup_range_lev2 :
    (V2 : Subgroup (projectiveSL 3 F)) ⊔ (lev2Hom (F := F)).range = Ln F := by
  apply le_antisymm
  · exact sup_le Subgroup.le_normalizer range_lev2_le_Ln
  · intro p hp
    rw [Ln, normalizer_V2_eq] at hp
    obtain ⟨M, hM, rfl⟩ := hp
    rw [q1_decomp hM, map_mul, map_mul]
    have h1 : proj 3 F (yMat (M.1 1 2 * q1Delta M)) ∈
        (V2 : Subgroup (projectiveSL 3 F)) := by
      show yP (M.1 1 2 * q1Delta M) ∈ (V2 : Subgroup (projectiveSL 3 F))
      exact mem_V2.mpr ⟨_, 0, by rw [wP_zero, mul_one]⟩
    have h2 : proj 3 F (wMat (M.1 0 2 * q1Delta M)) ∈
        (V2 : Subgroup (projectiveSL 3 F)) := by
      show wP (M.1 0 2 * q1Delta M) ∈ (V2 : Subgroup (projectiveSL 3 F))
      exact mem_V2.mpr ⟨0, _, by rw [yP_zero, one_mul]⟩
    have h12 : proj 3 F (yMat (M.1 1 2 * q1Delta M)) *
        proj 3 F (wMat (M.1 0 2 * q1Delta M)) ∈
        (V2 : Subgroup (projectiveSL 3 F)) ⊔ (lev2Hom (F := F)).range :=
      mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_left h2)
    have hD : proj 3 F (blk2SL (q1BlockGL M hM)) ∈
        (V2 : Subgroup (projectiveSL 3 F)) ⊔ (lev2Hom (F := F)).range :=
      Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨q1BlockGL M hM, rfl⟩)
    exact mul_mem h12 hD

private theorem V1_sup_range_lev1 :
    (V1 : Subgroup (projectiveSL 3 F)) ⊔ (lev1Hom (F := F)).range = Pt F := by
  apply le_antisymm
  · exact sup_le Subgroup.le_normalizer range_lev1_le_Pt
  · intro p hp
    rw [Pt, normalizer_V1_eq] at hp
    obtain ⟨M, hM, rfl⟩ := hp
    rw [q0_decomp hM, map_mul, proj_unit1Mat, ← mul_assoc]
    have h1 : xP (M.1 0 1 * (q0Delta M)⁻¹) ∈
        (V1 : Subgroup (projectiveSL 3 F)) :=
      mem_V1.mpr ⟨_, 0, by rw [wP_zero, mul_one]⟩
    have h2 : wP (M.1 0 2 * (q0Delta M)⁻¹) ∈
        (V1 : Subgroup (projectiveSL 3 F)) :=
      mem_V1.mpr ⟨0, _, by rw [xP_zero, one_mul]⟩
    have hD : proj 3 F (blk1SL (q0BlockGL M hM)) ∈
        (V1 : Subgroup (projectiveSL 3 F)) ⊔ (lev1Hom (F := F)).range :=
      Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨q0BlockGL M hM, rfl⟩)
    have hDa : proj 3 F (blk1SL (q0BlockGL M hM)) *
        xP (M.1 0 1 * (q0Delta M)⁻¹) ∈
        (V1 : Subgroup (projectiveSL 3 F)) ⊔ (lev1Hom (F := F)).range :=
      mul_mem hD (Subgroup.mem_sup_left h1)
    exact mul_mem hDa (Subgroup.mem_sup_left h2)

private theorem range_lev2_inf_V2 :
    (lev2Hom (F := F)).range ⊓ (V2 : Subgroup (projectiveSL 3 F)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro g ⟨hgR, hgV⟩
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hgR
  set M : Matrix.SpecialLinearGroup (Fin 3) F := blk2SL A with hMdef
  have hM : M ∈ Q3 F 1 :=
    mem_Q3_one_iff.mpr ⟨by simp [M, blk2SL], by simp [M, blk2SL]⟩
  have hΔ0 : q1Delta M ≠ 0 := q1Delta_ne_zero hM
  have hgV' : proj 3 F M ∈ (V2 : Subgroup (projectiveSL 3 F)) := hgV
  have hcomm : ∀ u ∈ (V2 : Subgroup (projectiveSL 3 F)),
      proj 3 F M * u * (proj 3 F M)⁻¹ = u := by
    intro u hu
    have huv := IsElemAbelian.comm (isElemAbelian_V2 (F := F)) hu hgV'
    calc proj 3 F M * u * (proj 3 F M)⁻¹ = u * proj 3 F M * (proj 3 F M)⁻¹ := by
          rw [← huv]
      _ = u := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have h1' : yP (q1Delta M * M.1 1 1) * wP (q1Delta M * M.1 0 1) = yP 1 := by
    have h := conj_yP_wP_Q3_one hM 1 0
    simp only [q1Delta, mul_one, mul_zero, add_zero, wP_zero, one_mul] at h ⊢
    rw [← h]
    exact hcomm (yP 1) (mem_V2.mpr ⟨1, 0, by rw [wP_zero, mul_one]⟩)
  have h1'' : yP (q1Delta M * M.1 1 1) * wP (q1Delta M * M.1 0 1) =
      yP 1 * wP 0 := by
    rw [wP_zero, mul_one]
    exact h1'
  obtain ⟨h11, h01⟩ := yP_wP_inj h1''
  have h0' : yP (q1Delta M * M.1 1 0) * wP (q1Delta M * M.1 0 0) = yP 0 * wP 1 := by
    have h := conj_yP_wP_Q3_one hM 0 1
    simp only [q1Delta, mul_one, mul_zero, zero_mul, add_zero, zero_add, yP_zero,
      one_mul] at h ⊢
    rw [← h]
    exact hcomm (wP 1) (mem_V2.mpr ⟨0, 1, by rw [yP_zero, one_mul]⟩)
  obtain ⟨h10, h00⟩ := yP_wP_inj h0'
  have hM00 : M.1 0 0 = (q1Delta M)⁻¹ := eq_inv_of_mul_eq_one_right h00
  have hM11 : M.1 1 1 = (q1Delta M)⁻¹ := eq_inv_of_mul_eq_one_right h11
  have hM01 : M.1 0 1 = 0 := (mul_eq_zero.mp h01).resolve_left hΔ0
  have hM10 : M.1 1 0 = 0 := (mul_eq_zero.mp h10).resolve_left hΔ0
  have hM22 : M.1 2 2 = (q1Delta M)⁻¹ := q1_bottom_right hM
  have hΔdef : q1Delta M = (q1Delta M)⁻¹ * (q1Delta M)⁻¹ := by
    change M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 =
      (q1Delta M)⁻¹ * (q1Delta M)⁻¹
    rw [hM00, hM11, hM01, hM10]
    ring
  have hΔ3 : q1Delta M ^ 3 = 1 := by
    have h := congrArg (fun x : F => x * q1Delta M ^ 2) hΔdef
    field_simp [hΔ0] at h
    simpa [pow_three, mul_assoc] using h
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 =
      ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ := by
    have h := hM00
    rw [hMdef] at h
    rw [show (blk2SL A).1 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 from rfl,
      q1Delta_blk2SL A] at h
    exact h
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 =
      ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ := by
    have h := hM11
    rw [hMdef] at h
    rw [show (blk2SL A).1 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 from rfl,
      q1Delta_blk2SL A] at h
    exact h
  have hA01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    simpa [hMdef, blk2SL] using hM01
  have hA10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [hMdef, blk2SL] using hM10
  have hMmat : (blk2SL A : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) (q1Delta (blk2SL A))⁻¹ := by
    rw [q1Delta_blk2SL A]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hA00, hA11, hA01, hA10, blk2SL]
  refine Subgroup.mem_bot.mpr ?_
  change proj 3 F M = 1
  rw [proj_eq_one_iff]
  refine mem_scalars.mpr ⟨(Units.mk0 (q1Delta M) hΔ0)⁻¹, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hΔ3,
      inv_one]
    rfl
  · simpa [hMdef] using hMmat

private theorem range_lev1_inf_V1 :
    (lev1Hom (F := F)).range ⊓ (V1 : Subgroup (projectiveSL 3 F)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro g ⟨hgR, hgV⟩
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hgR
  set M : Matrix.SpecialLinearGroup (Fin 3) F := blk1SL A with hMdef
  have hM : M ∈ Q3 F 0 :=
    mem_Q3_zero_iff.mpr ⟨by simp [M, blk1SL], by simp [M, blk1SL]⟩
  have hΔ0 : q0Delta M ≠ 0 := q0Delta_ne_zero hM
  have hgV' : proj 3 F M ∈ (V1 : Subgroup (projectiveSL 3 F)) := hgV
  have hcomm : ∀ u ∈ (V1 : Subgroup (projectiveSL 3 F)),
      proj 3 F M * u * (proj 3 F M)⁻¹ = u := by
    intro u hu
    have huv := IsElemAbelian.comm (isElemAbelian_V1 (F := F)) hu hgV'
    calc proj 3 F M * u * (proj 3 F M)⁻¹ = u * proj 3 F M * (proj 3 F M)⁻¹ := by
          rw [← huv]
      _ = u := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have h1' : xP (q0Delta M ^ 2 * M.1 2 2) * wP (q0Delta M ^ 2 * M.1 1 2) = xP 1 := by
    have h := conj_xP_wP_Q3_zero hM 1 0
    simp only [q0Delta, mul_one, mul_zero, zero_mul, add_zero, wP_zero, one_mul] at h ⊢
    rw [← h]
    exact hcomm (xP 1) (mem_V1.mpr ⟨1, 0, by rw [wP_zero, mul_one]⟩)
  have h1'' : xP (q0Delta M ^ 2 * M.1 2 2) * wP (q0Delta M ^ 2 * M.1 1 2) =
      xP 1 * wP 0 := by
    rw [wP_zero, mul_one]
    exact h1'
  obtain ⟨h22, h12⟩ := xP_mul_wP_inj h1''
  have h0' : xP (q0Delta M ^ 2 * M.1 2 1) * wP (q0Delta M ^ 2 * M.1 1 1) =
      xP 0 * wP 1 := by
    have h := conj_xP_wP_Q3_zero hM 0 1
    simp only [q0Delta, mul_one, mul_zero, zero_mul, add_zero, zero_add, xP_zero,
      one_mul] at h ⊢
    rw [← h]
    exact hcomm (wP 1) (mem_V1.mpr ⟨0, 1, by rw [xP_zero, one_mul]⟩)
  obtain ⟨h21, h11⟩ := xP_mul_wP_inj h0'
  have hM22 : M.1 2 2 = ((q0Delta M) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h22
  have hM11 : M.1 1 1 = ((q0Delta M) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h11
  have hM12 : M.1 1 2 = 0 :=
    (mul_eq_zero.mp h12).resolve_left (pow_ne_zero 2 hΔ0)
  have hM21 : M.1 2 1 = 0 :=
    (mul_eq_zero.mp h21).resolve_left (pow_ne_zero 2 hΔ0)
  have hprod : q0Delta M * (M.1 1 1 * M.1 2 2 - M.1 1 2 * M.1 2 1) = 1 :=
    det_V1 (mem_Q3_zero_iff.mp hM).1 (mem_Q3_zero_iff.mp hM).2
  rw [hM11, hM22, hM12, hM21] at hprod
  have hΔ3 : q0Delta M ^ 3 = 1 := by
    field_simp [hΔ0] at hprod
    simpa using hprod.symm
  have hsq : ((q0Delta M) ^ 2)⁻¹ = q0Delta M := by
    have h : (q0Delta M) ^ 2 * q0Delta M = 1 := by
      rw [← pow_succ]
      simpa using hΔ3
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = q0Delta M := by
    have h := hM11
    rw [hMdef] at h
    rw [show (blk1SL A).1 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 from rfl, hsq] at h
    exact h
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = q0Delta M := by
    have h := hM22
    rw [hMdef] at h
    rw [show (blk1SL A).1 2 2 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 from rfl, hsq] at h
    exact h
  have hA12 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h := hM12
    rw [hMdef] at h
    simpa [blk1SL] using h
  have hA21 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h := hM21
    rw [hMdef] at h
    simpa [blk1SL] using h
  have hq0 : q0Delta M = ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ := by
    rw [hMdef]
    rfl
  have hMmat : (blk1SL A : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) (q0Delta M) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, hq0, blk1SL, hA00, hA11, hA12, hA21]
  refine Subgroup.mem_bot.mpr ?_
  change proj 3 F M = 1
  rw [proj_eq_one_iff]
  refine mem_scalars.mpr ⟨Units.mk0 (q0Delta M) hΔ0, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hΔ3]
    rfl
  · simpa [hMdef] using hMmat

private theorem linAction_ln :
    LinAction (Ln F) (V2 : Subgroup (projectiveSL 3 F)) (cubeDetGL F) := by
  refine ⟨vecV2, ?_, ?_⟩
  · intro p hp
    rw [Ln, normalizer_V2_eq] at hp
    obtain ⟨M, hM, rfl⟩ := hp
    exact ⟨q1ActionGL M hM, q1ActionGL_mem M hM, actsByMatrix_q1 hM⟩
  · intro B hB
    rw [cubeDetGL, Subgroup.mem_comap, MonoidHom.mem_range] at hB
    obtain ⟨e, he⟩ := hB
    have he3 : e ^ 3 = Matrix.GeneralLinearGroup.det B := by simpa using he
    set A : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) (e⁻¹) * B with hAdef
    have hdetA : Matrix.GeneralLinearGroup.det A = e := by
      calc Matrix.GeneralLinearGroup.det A =
          Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (e⁻¹)) *
            Matrix.GeneralLinearGroup.det B := by rw [hAdef, map_mul]
        _ = (e⁻¹) ^ 2 * e ^ 3 := by simp [he3]
        _ = e := by group
    have hAval : (A : Matrix (Fin 2) (Fin 2) F) =
        ((e⁻¹ : Fˣ) : F) • (B : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAdef, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two]
    have hq1 : q1ActionMat (blk2SL A) = (B : Matrix (Fin 2) (Fin 2) F) := by
      rw [q1ActionMat_blk2SL A, hdetA, hAval]
      ext i j
      simp [Matrix.smul_apply]
      all_goals field_simp [e.ne_zero]
    have hM : blk2SL A ∈ Q3 F 1 :=
      mem_Q3_one_iff.mpr ⟨by simp [blk2SL], by simp [blk2SL]⟩
    refine ⟨lev2Hom A, range_lev2_le_Ln (MonoidHom.mem_range.mpr ⟨A, rfl⟩), ?_⟩
    change ActsByMatrix vecV2 (proj 3 F (blk2SL A)) (B : Matrix (Fin 2) (Fin 2) F)
    simpa [hq1] using actsByMatrix_q1_mat hM

private theorem linAction_pt :
    LinAction (Pt F) (V1 : Subgroup (projectiveSL 3 F)) (cubeDetGL F) := by
  refine ⟨vecV1, ?_, ?_⟩
  · intro p hp
    rw [Pt, normalizer_V1_eq] at hp
    obtain ⟨M, hM, rfl⟩ := hp
    exact ⟨q0ActionGL M hM, q0ActionGL_mem M hM, actsByMatrix_q0 hM⟩
  · intro B hB
    rw [cubeDetGL, Subgroup.mem_comap, MonoidHom.mem_range] at hB
    obtain ⟨e, he⟩ := hB
    have he3 : e ^ 3 = Matrix.GeneralLinearGroup.det B := by simpa using he
    have hBdet : (B : Matrix (Fin 2) (Fin 2) F).det = (e : F) ^ 3 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val he3.symm
    set A : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((((e : F)⁻¹) ^ 2) • swapMat (B : Matrix (Fin 2) (Fin 2) F)) (by
        rw [Matrix.det_smul, Fintype.card_fin, swapMat_det, hBdet]
        exact mul_ne_zero (pow_ne_zero 2 (pow_ne_zero 2 (inv_ne_zero e.ne_zero)))
          (pow_ne_zero 3 e.ne_zero)) with hAdef
    have hAval : (A : Matrix (Fin 2) (Fin 2) F) =
        (((e : F)⁻¹) ^ 2) • swapMat (B : Matrix (Fin 2) (Fin 2) F) := by
      rw [hAdef]
      rfl
    have hdetA : ((Matrix.GeneralLinearGroup.det A : Fˣ) : F) = (e : F)⁻¹ := by
      change (((((e : F)⁻¹) ^ 2) • swapMat (B : Matrix (Fin 2) (Fin 2) F)).det) =
        (e : F)⁻¹
      rw [Matrix.det_smul, Fintype.card_fin, swapMat_det, hBdet]
      field_simp [e.ne_zero]
    have hq0d : q0Delta (blk1SL A) = (e : F) := by
      change ((Matrix.GeneralLinearGroup.det A : Fˣ) : F)⁻¹ = (e : F)
      rw [hdetA]
      simp
    have hq1 : q0ActionMat (blk1SL A) = (B : Matrix (Fin 2) (Fin 2) F) := by
      rw [q0ActionMat_blk1SL A, hdetA]
      simp only [inv_inv]
      rw [hAval, swapMat_smul, swapMat_swapMat]
      ext i j
      simp [Matrix.smul_apply]
      all_goals field_simp [e.ne_zero]
    have hM : blk1SL A ∈ Q3 F 0 :=
      mem_Q3_zero_iff.mpr ⟨by simp [blk1SL], by simp [blk1SL]⟩
    refine ⟨lev1Hom A, range_lev1_le_Pt (MonoidHom.mem_range.mpr ⟨A, rfl⟩), ?_⟩
    change ActsByMatrix vecV1 (proj 3 F (blk1SL A)) (B : Matrix (Fin 2) (Fin 2) F)
    simpa [hq1] using actsByMatrix_q0_mat hM

theorem isLinSemidirect_Ln :
    IsLinSemidirect (Ln F) (V2 : Subgroup (projectiveSL 3 F)) (cubeDetGL F) where
  le := Subgroup.le_normalizer
  normal := by
    simpa [Ln] using (Subgroup.le_normalizer :
      (V2 : Subgroup (projectiveSL 3 F)) ≤
        Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)))
  cent := by
    have h : CharTwo (Ln F) :=
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F)).charTwo₂
    simpa [CharTwo, Ln, core_V2] using h
  split := ⟨(lev2Hom (F := F)).range, range_lev2_le_Ln, range_lev2_inf_V2,
    V2_sup_range_lev2⟩
  act := linAction_ln

theorem isLinSemidirect_Pt :
    IsLinSemidirect (Pt F) (V1 : Subgroup (projectiveSL 3 F)) (cubeDetGL F) where
  le := Subgroup.le_normalizer
  normal := by
    simpa [Pt] using (Subgroup.le_normalizer :
      (V1 : Subgroup (projectiveSL 3 F)) ≤
        Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
          Set (projectiveSL 3 F)))
  cent := by
    have h : CharTwo (Pt F) :=
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F)).charTwo₁
    simpa [CharTwo, Pt, core_V1] using h
  split := ⟨(lev1Hom (F := F)).range, range_lev1_le_Pt, range_lev1_inf_V1,
    V1_sup_range_lev1⟩
  act := linAction_pt

end CFSG.Quasithin.F112R.St84
