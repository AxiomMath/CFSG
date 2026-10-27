module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix

namespace NbrGraphLinear

variable {d : ℕ} {K : Type} [Field K]

theorem symm_congr_conjAut_mem (A : GL (Fin d) K) :
    (MulAut.congr (TypeA.recipeEquiv d K)).symm (conjAut d K A) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
  refine ⟨A, Set.mem_univ _, fun h h' hh' => ?_⟩
  rw [MulAut.congr_symm_apply]
  change (TypeA.recipeEquiv d K).symm
    (conjAut d K A (TypeA.recipeEquiv d K (LargeEvenProjMk _ h))) = LargeEvenProjMk _ h'
  rw [TypeA.recipeEquiv_mk, conjAut_proj, MulEquiv.symm_apply_eq, TypeA.recipeEquiv_mk]
  congr 1
  ext i j
  rw [coe_slConjugation, TypeA.coe_slKerEquiv, TypeA.coe_slKerEquiv, hh', Units.val_mul,
    Units.val_mul]

theorem symm_congr_fieldAut_mem (σ : K ≃+* K) :
    (MulAut.congr (TypeA.recipeEquiv d K)).symm (fieldAut d K σ) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  rw [MulAut.congr_symm_apply]
  change (TypeA.recipeEquiv d K).symm
    (fieldAut d K σ (TypeA.recipeEquiv d K (LargeEvenProjMk _ h))) = LargeEvenProjMk _ h'
  rw [TypeA.recipeEquiv_mk, fieldAut_proj, MulEquiv.symm_apply_eq, TypeA.recipeEquiv_mk]
  congr 1
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, TypeA.coe_slKerEquiv, TypeA.coe_slKerEquiv, hh']
  rfl

theorem ggOddAutInnField_linear_of_three_le [Finite K] (hd : 3 ≤ d) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  intro φ hφ
  set c := MulAut.congr (TypeA.recipeEquiv d K) with hc
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hd).2 (c φ)
  have hε0 : ε = 0 :=
    HypSixTypeA.graph_exp_eq_zero hd hp hε (by rw [← hα, ← map_pow, hφ, map_one])
  subst hε0
  rw [pow_zero, mul_one] at hα
  refine ⟨c.symm (conjAut d K A), symm_congr_conjAut_mem A, c.symm (fieldAut d K σ),
    Subgroup.subset_closure (symm_congr_fieldAut_mem σ), ?_⟩
  rw [← map_mul, ← hα, MulEquiv.symm_apply_apply]

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable (K) in
@[expose] noncomputable def recipeEquivTwo :
    LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃* PSL2 K :=
  (TypeA.recipeEquiv 2 K).trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 K))

theorem recipeEquivTwo_mk (h : LargeEvenSLGroup (Fin 2) K) :
    recipeEquivTwo K (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K) h) =
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K)) (TypeA.slKerEquiv 2 K h) :=
  rfl

theorem toGL_slKerEquiv (h : LargeEvenSLGroup (Fin 2) K) :
    SpecialLinearGroup.toGL (TypeA.slKerEquiv 2 K h) = (h : GL (Fin 2) K) :=
  Units.ext rfl

theorem symm_congr_pglAction_mem (A : GL (Fin 2) K) :
    (MulAut.congr (recipeEquivTwo K)).symm (pglAction K (ProjGenLinGroup.mk A)) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ := by
  refine ⟨A, Set.mem_univ _, fun h h' hh' => ?_⟩
  rw [MulAut.congr_symm_apply]
  change (recipeEquivTwo K).symm
    (pglAction K (ProjGenLinGroup.mk A) (recipeEquivTwo K (LargeEvenProjMk _ h))) =
      LargeEvenProjMk _ h'
  rw [MulEquiv.symm_apply_eq, recipeEquivTwo_mk, recipeEquivTwo_mk]
  apply ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    ProjectiveSpecialLinearGroup.toPGL_mk, ProjectiveSpecialLinearGroup.toPGL_mk,
    toGL_slKerEquiv, toGL_slKerEquiv, hh', ← map_inv, ← map_mul, ← map_mul]

theorem symm_congr_psl2FieldAut_mem (σ : K ≃+* K) :
    (MulAut.congr (recipeEquivTwo K)).symm (psl2FieldAut K σ) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  rw [MulAut.congr_symm_apply]
  change (recipeEquivTwo K).symm
    (psl2FieldAut K σ (recipeEquivTwo K (LargeEvenProjMk _ h))) = LargeEvenProjMk _ h'
  rw [MulEquiv.symm_apply_eq, recipeEquivTwo_mk, recipeEquivTwo_mk, psl2FieldAut_apply,
    psl2RingEquiv_mk]
  congr 1
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, TypeA.coe_slKerEquiv, TypeA.coe_slKerEquiv, hh']
  rfl

theorem ggOddAutInnField_linear_two [Finite K] (p : ℕ) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K))) := by
  intro φ _
  set c := MulAut.congr (recipeEquivTwo K) with hc
  obtain ⟨x, hx⟩ := semilinearAction_surjective K (c φ)
  obtain ⟨A, hA⟩ := ProjGenLinGroup.mk_surjective x.left
  have hφ : c φ = pglAction K (ProjGenLinGroup.mk A) * psl2FieldAut K x.right := by
    rw [← hx, hA]
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  refine ⟨c.symm (pglAction K (ProjGenLinGroup.mk A)), symm_congr_pglAction_mem A,
    c.symm (psl2FieldAut K x.right),
    Subgroup.subset_closure (symm_congr_psl2FieldAut_mem x.right), ?_⟩
  rw [← map_mul, ← hφ, MulEquiv.symm_apply_apply]

theorem ggOddAutInnField_linear [Finite K] (hd : 2 ≤ d) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    exact ggOddAutInnField_linear_two p
  · exact ggOddAutInnField_linear_of_three_le h hp

theorem recipeLinear_all {N : ℕ} {Q Q₀ : LargeEvenRawCont}
    (hQ : ∀ (K : Type) [Field K] [Finite K], Nat.card K = N →
      Q (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))))
    (h : LargeEvenRecipeLinear d N Q₀) :
    LargeEvenRecipeLinear d N fun R _ I F => Q₀ R I F ∧ Q R I F := by
  obtain ⟨K, _, _, hK, hQ₀⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ₀, hQ K hK⟩

end NbrGraphLinear

open NbrGraphLinear

@[expose] def GGLinearRecipeLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2)

theorem ggOddAutOn_linear : GGOddAutOn GGLinearRecipeLabel := by
  intro p lab hp hp2 hlab hS _ Q₀ h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · have hl1 : 1 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine recipeLinear_all (fun K _ _ _ => ?_) h
    exact fun _ _ => ggOddAutInnField_linear (by omega) hodd
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine recipeLinear_all (fun K _ _ _ => ?_) h
    exact fun _ _ => ggOddAutInnField_linear (by omega) hodd
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine recipeLinear_all (fun K _ _ _ => ?_) h
    exact fun _ _ => ggOddAutInnField_linear le_rfl hodd

end CFSG.StandardType
