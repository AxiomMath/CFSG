module

public import CFSG.RankThree.FFModules.Transvections

public section

namespace CFSG.RankThree.FFModules

open scoped MatrixGroups
open Matrix Module

variable {K : Type*} [Field K]

theorem map_map_toLin'_inv (S : Submodule K (Fin 3 → K)) (h : SL(3, K)) :
    (S.map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) K))).map
      (Matrix.toLin' ((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) = S := by
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one, Submodule.map_id]

theorem conj_mem_transvectionGroup {S : Submodule K (Fin 3 → K)} {g : SL(3, K)}
    (hg : g ∈ transvectionGroup S) (h : SL(3, K)) :
    h * g * h⁻¹ ∈ transvectionGroup (S.map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) K))) := by
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.1 hw
    rw [Matrix.toLin'_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mulVec_inv_mulVec, hg.1 s hs]
  · refine Submodule.mem_map.2 ⟨(g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) -
        ((h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ w, hg.2 _, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_sub, mulVec_mulVec_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mem_transvectionGroup_iff_conj (S : Submodule K (Fin 3 → K)) (h y : SL(3, K)) :
    y ∈ transvectionGroup S ↔
      h * y * h⁻¹ ∈ transvectionGroup (S.map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) K))) := by
  refine ⟨fun hy => conj_mem_transvectionGroup hy h, fun hy => ?_⟩
  have := conj_mem_transvectionGroup hy h⁻¹
  rwa [map_map_toLin'_inv, inv_inv, show h⁻¹ * (h * y * h⁻¹) * h = y by group] at this

theorem mem_normalizer_of_mulVec_eq {v : Fin 3 → K} {h : SL(3, K)}
    (hv : (h : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) :
    h ∈ Subgroup.normalizer (transvectionGroup (K ∙ v) : Set SL(3, K)) := by
  have hS : (K ∙ v).map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) K)) = K ∙ v := by
    rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hv]
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  rw [mem_transvectionGroup_iff_conj (K ∙ v) h y, hS]

theorem transvection_mem_single {i j : Fin 3} (hij : i ≠ j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈
      transvectionGroup (K ∙ (Pi.single i 1 : Fin 3 → K)) := by
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [Matrix.mulVec_smul]
    congr 1
    rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq]
    simp [Ne.symm hij]
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
      add_sub_cancel_left, Matrix.single_mulVec_eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem transvection_mulVec_single_of_ne {k l m : Fin 3} (hkl : k ≠ l) (hml : m ≠ l) (d : K) :
    ((SpecialLinearGroup.transvection hkl d : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (Pi.single m 1 : Fin 3 → K) = Pi.single m 1 := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  simp [Ne.symm hml]

theorem exists_map_span_eq_single {v : Fin 3 → K} (hv : v ≠ 0) (i : Fin 3) :
    ∃ g : SL(3, K), (K ∙ v).map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) =
      K ∙ (Pi.single i 1 : Fin 3 → K) := by
  classical
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : SL(3, K), ((g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) i ≠ 0 := by
    by_cases hvi : v i = 0
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hv
      have hai : a ≠ i := by
        rintro rfl
        exact ha hvi
      refine ⟨transvectionOf (Pi.single i 1) (Pi.single a 1) (by simp [hai]), ?_⟩
      rw [transvectionOf_mulVec]
      simpa [hvi, single_one_dotProduct] using ha
    · exact ⟨1, by simpa using hvi⟩
  set w := (g₁ : Matrix (Fin 3) (Fin 3) K) *ᵥ v with hw
  set u : Fin 3 → K := -(w i)⁻¹ • (w - w i • Pi.single i 1) with hu
  have hu0 : (Pi.single i 1 : Fin 3 → K) ⬝ᵥ u = 0 := by
    rw [single_one_dotProduct, hu]
    simp
  refine ⟨transvectionOf u (Pi.single i 1) hu0 * g₁, ?_⟩
  have himg : ((transvectionOf u (Pi.single i 1) hu0 * g₁ : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = w i • Pi.single i 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← hw, transvectionOf_mulVec,
      single_one_dotProduct, hu, smul_smul, mul_neg, mul_inv_cancel₀ hg₁, neg_one_smul]
    abel
  rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, himg,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hg₁)]

@[expose] def dualHom : SL(3, K) →* SL(3, K) where
  toFun g := ⟨dualMat (F := K) g, by
    rw [dualMat, Matrix.det_transpose]
    exact ((g⁻¹ : SL(3, K))).2⟩
  map_one' := Subtype.ext (dualMat_one (F := K))
  map_mul' g h := Subtype.ext (dualMat_mul (F := K) g h)

theorem coe_dualHom (g : SL(3, K)) :
    ((dualHom g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = dualMat g := rfl

theorem dualHom_injective : Function.Injective (dualHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [← dualMat_eq_one_iff, ← coe_dualHom, hg, Matrix.SpecialLinearGroup.coe_one]

theorem dualHom_mem {S : Submodule K (Fin 3 → K)} {g : SL(3, K)} (hg : g ∈ transvectionGroup S) :
    dualHom g ∈ transvectionGroup (dotOrth S) := by
  refine ⟨fun x hx => ?_, fun x s hs => ?_⟩
  · rw [coe_dualHom, dualMat_mulVec_eq_iff]
    intro y
    exact hx _ (hg.2 y)
  · have hinv := (inv_mem hg).1 s hs
    rw [coe_dualHom, dualMat, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hinv, sub_self]

end CFSG.RankThree.FFModules
