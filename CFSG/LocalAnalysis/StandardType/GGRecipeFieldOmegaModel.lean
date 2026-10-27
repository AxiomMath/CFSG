module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

section Graph

variable {H R : Type*} [Group H] [Group R]

theorem eq_of_graphAut {π : H →* R} (hπ : Function.Surjective π) {rel : H → H → Prop}
    {φ ψ : MulAut R} (hφ : LargeEvenGraphAut π rel φ) (hψ : LargeEvenGraphAut π rel ψ)
    (hex : ∀ h, ∃ h', rel h h') : φ = ψ := by
  ext x
  obtain ⟨h, rfl⟩ := hπ x
  obtain ⟨h', hh'⟩ := hex h
  rw [hφ h h' hh', hψ h h' hh']

theorem graphAut_congr_symm {Γ : Type*} [Group Γ] (π : H →* R) (Θ : R ≃* Γ) (ψ : MulAut Γ)
    {rel : H → H → Prop} (h : ∀ x y, rel x y → ψ (Θ (π x)) = Θ (π y)) :
    LargeEvenGraphAut π rel ((MulAut.congr Θ).symm ψ) := by
  intro x y hxy
  change Θ.symm (ψ (Θ (π x))) = π y
  rw [h x y hxy, MulEquiv.symm_apply_apply]

end Graph

namespace RecipeFieldOmega

section Reindex

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem glFieldAut_apply_val (σ : K ≃+* K) (A : GL ι K) :
    (glFieldAut ι K σ A).val = A.val.map σ := rfl

theorem glFieldAut_reindex (e : ι ≃ Fin d) (σ : K ≃+* K) (A : GL ι K) :
    glFieldAut (Fin d) K σ (reindexMatrixEquiv e A) =
      reindexMatrixEquiv e (glFieldAut ι K σ A) := by
  apply Units.ext
  ext i j
  rfl

end Reindex

section Plus

variable {K : Type} [Field K] {m : ℕ}

variable (K m) in
theorem omegaPlus_eq : LargeEvenOmega (LargeEvenQPlus K m) = StatedOmega ⇑(quadPlus m K) := by
  rw [coe_quadPlus]

variable [CharP K 2]

omit [CharP K 2] in
variable (K m) in
theorem coordinateQuadPlus_eq :
    coordinateQuadPlus m K = reindexQuadraticForm (plusIndexEquiv m) (quadPlus m K) := rfl

@[expose] noncomputable def plusEquiv (hm : 1 ≤ m) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) ≃* matrixDerived (coordinateQuadPlus m K) :=
  (TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) hm)).symm.trans
    ((MulEquiv.subgroupCongr (omegaPlus_eq K m)).trans
      ((statedMatrixDerivedEquiv (plusIndexEquiv m) (quadPlus m K)).trans
        (MulEquiv.subgroupCongr (congrArg matrixDerived (coordinateQuadPlus_eq K m).symm))))

theorem plusEquiv_mk_val (hm : 1 ≤ m) (h : LargeEvenOmega (LargeEvenQPlus K m)) :
    ((plusEquiv hm (LargeEvenProjMk _ h) : matrixDerived (coordinateQuadPlus m K)) :
      GL (Fin (2 * m)) K) = reindexMatrixEquiv (plusIndexEquiv m) (h : GL (Fin m ⊕ Fin m) K) := by
  have e : LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)) h =
      TableBOrth.projMkEquiv (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (K := K) hm) h :=
    (TableBOrth.projMkEquiv_apply _ h).symm
  rw [e, plusEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, statedMatrixDerivedEquiv_val,
    MulEquiv.subgroupCongr_apply]

omit [CharP K 2] in
theorem proj_surjective_plus :
    Function.Surjective (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))) :=
  QuotientGroup.mk'_surjective _

omit [CharP K 2] in
theorem fieldAutP_apply_val (σ : K ≃+* K) (X : matrixDerived (coordinateQuadPlus m K)) :
    ((AutOm.fieldAutP m σ X : matrixDerived (coordinateQuadPlus m K)) : GL (Fin (2 * m)) K) =
      glFieldAut (Fin (2 * m)) K σ X.val := by
  rw [AutOm.fieldAutP_apply]
  exact CFSG.RankThree.PartOne.KCOrthogonalSubfield.matrixDerivedConjugation_fieldPair_val _ σ _ X

theorem graphAut_fieldAutP (hm : 1 ≤ m) (σ : K ≃+* K) :
    LargeEvenGraphAut (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))
      (fun h h' => ((h' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        ((h : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ)
      ((MulAut.congr (plusEquiv (K := K) hm)).symm (AutOm.fieldAutP m σ)) := by
  refine graphAut_congr_symm _ _ _ fun x y hxy => Subtype.ext ?_
  rw [fieldAutP_apply_val, plusEquiv_mk_val, plusEquiv_mk_val, glFieldAut_reindex]
  congr 1
  exact Units.ext hxy.symm

theorem exists_map_mem_plus (hm : 1 ≤ m) (σ : K ≃+* K) (h : LargeEvenOmega (LargeEvenQPlus K m)) :
    ∃ h' : LargeEvenOmega (LargeEvenQPlus K m),
      ((h' : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        ((h : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map σ := by
  set Θ := plusEquiv (K := K) hm
  obtain ⟨h', hh'⟩ := proj_surjective_plus (Θ.symm (AutOm.fieldAutP m σ (Θ (LargeEvenProjMk _ h))))
  refine ⟨h', ?_⟩
  have e1 := congrArg (fun x => ((Θ x : matrixDerived (coordinateQuadPlus m K)) :
    GL (Fin (2 * m)) K)) hh'
  simp only [MulEquiv.apply_symm_apply] at e1
  rw [plusEquiv_mk_val, fieldAutP_apply_val, plusEquiv_mk_val, glFieldAut_reindex] at e1
  have e2 := congrArg Units.val ((reindexMatrixEquiv (plusIndexEquiv m)).injective e1)
  exact e2

theorem congr_plusEquiv_of_mem_field (hm : 1 ≤ m) {φ : MulAut
    (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) :
    ∃ σ : K ≃+* K, MulAut.congr (plusEquiv hm) φ = AutOm.fieldAutP m σ := by
  obtain ⟨σ, hσ⟩ := hφ
  refine ⟨σ, ?_⟩
  rw [← MulEquiv.eq_symm_apply]
  exact eq_of_graphAut proj_surjective_plus hσ (graphAut_fieldAutP hm σ)
    (exists_map_mem_plus hm σ)

theorem exists_mem_field_congr_plusEquiv (hm : 1 ≤ m) (σ : K ≃+* K) :
    ∃ φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m))),
      MulAut.congr (plusEquiv hm) φ = AutOm.fieldAutP m σ :=
  ⟨_, ⟨σ, graphAut_fieldAutP hm σ⟩, MulEquiv.apply_symm_apply _ _⟩

end Plus

end RecipeFieldOmega

end CFSG.StandardType
