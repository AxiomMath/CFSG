module

public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7SiegelGroup
public import CFSG.LocalAnalysis.StandardType.GGD4SmithParabolic
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.Quasithin.SmithCurtis QuadraticMap Matrix

theorem isSimpleRep_of_addSubgroup {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] {ρ : Representation k G V}
    (h : ∀ A : AddSubgroup V, (∀ g y, y ∈ A → ρ g y ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ∃ g y, ρ g y ≠ y) : IsSimpleRep ρ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨g, y, hy⟩ := hne
    exact ⟨y, ρ g y, Ne.symm hy⟩
  · intro W hW
    rcases h W.toAddSubgroup hW with hbot | htop
    · left
      apply Submodule.toAddSubgroup_injective
      simpa using hbot
    · right
      apply Submodule.toAddSubgroup_injective
      simpa using htop

@[expose] noncomputable def reindexOm8 (K : Type) [Field K] :
    StatedOmega (StatedQuadPlus 4 K) ≃* CFSG.StandardType.Triality.Om8 K :=
  statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)

@[expose] noncomputable def conjOm8 {K : Type} [Field K]
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    CFSG.StandardType.Triality.Om8 K ≃* StatedOmega (StatedQuadPlus 4 K) :=
  (reindexOm8 K).symm.trans (MulAut.conj A)

@[expose] noncomputable def conjPhi {K : Type} [Field K]
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  (reindexVectorEquiv (plusIndexEquiv 4)).symm.trans (toLinEquiv (Fin 4 ⊕ Fin 4) K A.val)

theorem conjPhi_pvec {K : Type} [Field K]
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    conjPhi A (CFSG.StandardType.AutOm.pvec (1 : Fin 4) true) =
      (((A.val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
        CFSG.LieType.Universal.Spin.plusVec 4 K (1 : Fin 4) true) := by
  simp only [conjPhi, CFSG.StandardType.AutOm.pvec, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, toLinEquiv_apply]

theorem conjPhi_isometry {K : Type} [Field K]
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    ∀ x : Fin (2 * 4) → K,
      quadPlus 4 K (conjPhi A x) = coordinateQuadPlus 4 K x := by
  intro x
  have hiso : ∀ v : Fin 4 ⊕ Fin 4 → K,
      quadPlus 4 K (A.val *ᵥ v) = quadPlus 4 K v := by
    intro v
    have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
      (f := StatedQuadPlus 4 K) A.2 v
    simpa only [CFSG.LieType.Universal.Spin.coe_quadPlus] using h
  have h2 : coordinateQuadPlus 4 K x =
      quadPlus 4 K ((reindexVectorEquiv (plusIndexEquiv 4)).symm x) := by
    rw [coordinateQuadPlus, reindexQuadraticForm_apply]
    rfl
  rw [h2]
  exact hiso _

theorem conjOm8_mulVec_conjPhi {K : Type} [Field K]
    (A : StatedOmega (StatedQuadPlus 4 K)) :
    ∀ (g : CFSG.StandardType.Triality.Om8 K) (x : Fin (2 * 4) → K),
      (((conjOm8 A g : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ conjPhi A x) =
        conjPhi A ((g : GL (Fin (2 * 4)) K) *ᵥ x) := by
  intro g x
  set y : Fin 4 ⊕ Fin 4 → K := (reindexVectorEquiv (plusIndexEquiv 4)).symm x with hy
  have hθ_val : (conjOm8 A g).val =
      A.val * ((reindexOm8 K).symm g).val * A.val⁻¹ := by
    simp only [conjOm8, reindexOm8, MulEquiv.trans_apply, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv]
  have hB : ((((reindexOm8 K).symm g).val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ y =
      (reindexVectorEquiv (plusIndexEquiv 4)).symm
        ((g : GL (Fin (2 * 4)) K) *ᵥ x) := by
    change ((((statedDerivedReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K)
      (coe_quadPlus 4 K)).symm g).val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ y = _
    rw [hy]
    simpa only [matrixLinearEquiv_apply, toLinEquiv_apply] using
      statedDerivedReindexEquiv_symm_vector (plusIndexEquiv 4) (quadPlus 4 K)
        (coe_quadPlus 4 K) g x
  change (((conjOm8 A g).val : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      (((A.val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ y) =
    ((A.val : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      (reindexVectorEquiv (plusIndexEquiv 4)).symm
        ((g : GL (Fin (2 * 4)) K) *ᵥ x)
  rw [hθ_val]
  change ((((A.val * ((reindexOm8 K).symm g).val * A.val⁻¹ :
        GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      (((A.val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ y))) =
    ((A.val : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ
      (reindexVectorEquiv (plusIndexEquiv 4)).symm
        ((g : GL (Fin (2 * 4)) K) *ᵥ x)
  rw [Matrix.mulVec_mulVec]
  have hcancel : (((A.val * ((reindexOm8 K).symm g).val * A.val⁻¹ :
        GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *
      ((A.val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)) =
      ((A.val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *
      ((((reindexOm8 K).symm g).val : GL (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rw [hcancel, ← Matrix.mulVec_mulVec, hB]

theorem exists_om8_stated_transport {K : Type} [Field K] [Finite K] [CharP K 2]
    {e : Fin 4 ⊕ Fin 4 → K} (he0 : e ≠ 0) (heS : StatedQuadPlus 4 K e = 0) :
    ∃ (θ : CFSG.StandardType.Triality.Om8 K ≃* StatedOmega (StatedQuadPlus 4 K))
      (φ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)),
      φ (CFSG.StandardType.AutOm.pvec (1 : Fin 4) true) = e ∧
      (∀ x : Fin (2 * 4) → K,
        quadPlus 4 K (φ x) = coordinateQuadPlus 4 K x) ∧
      ∀ (g : CFSG.StandardType.Triality.Om8 K) (x : Fin (2 * 4) → K),
        (((θ g : GL (Fin 4 ⊕ Fin 4) K) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ φ x) =
          φ ((g : GL (Fin (2 * 4)) K) *ᵥ x) := by
  have hx0 : CFSG.LieType.Universal.Spin.plusVec 4 K (1 : Fin 4) true ≠ 0 := by
    rw [CFSG.LieType.Universal.Spin.plusVec_true]
    exact Pi.single_ne_zero_iff.mpr one_ne_zero
  have hQe : quadPlus 4 K (CFSG.LieType.Universal.Spin.plusVec 4 K (1 : Fin 4) true) =
      quadPlus 4 K e := by
    rw [CFSG.LieType.Universal.Spin.quadPlus_plusVec,
      CFSG.LieType.Universal.Spin.coe_quadPlus]
    exact heS.symm
  obtain ⟨A, hA, hAe⟩ := statedOmegaPlus_exists_mulVec_eq (m := 4)
    (x := CFSG.LieType.Universal.Spin.plusVec 4 K (1 : Fin 4) true) (y := e)
    (by norm_num) hx0 he0 hQe
  refine ⟨conjOm8 ⟨A, hA⟩, conjPhi ⟨A, hA⟩, ?_, ?_, ?_⟩
  · rw [conjPhi_pvec, hAe]
  · exact conjPhi_isometry ⟨A, hA⟩
  · exact conjOm8_mulVec_conjPhi ⟨A, hA⟩

theorem smithOmegaPlusEight_of_om8
    (h : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (Y : Type) [AddCommGroup Y] [Module K Y]
      (ρ : Representation K (CFSG.StandardType.Triality.Om8 K) Y),
      CFSG.Quasithin.SmithCurtis.IsSimpleRep ρ → ∀ X : Submodule K Y,
      (∀ g : CFSG.StandardType.Triality.Om8 K, (g : GL (Fin (2 * 4)) K) ∈
          rootGroupGL (coordinateQuadPlus 4 K) (CFSG.StandardType.AutOm.pvec 1 true) →
          ∀ y ∈ X, ρ g y = y) →
      (∀ g : CFSG.StandardType.Triality.Om8 K, (g : GL (Fin (2 * 4)) K) ∈
          lineStabilizer (coordinateQuadPlus 4 K) (CFSG.StandardType.AutOm.pvec 1 true) →
          ∀ y ∈ X, ρ g y ∈ X) →
      X = ⊥ ∨ ∀ y : Y, (∀ g : CFSG.StandardType.Triality.Om8 K,
          (g : GL (Fin (2 * 4)) K) ∈
            rootGroupGL (coordinateQuadPlus 4 K) (CFSG.StandardType.AutOm.pvec 1 true) →
          ρ g y = y) → y ∈ X) :
    SmithOmegaPlusEightStatement := by
  intro K _ _ _ Y _ _ _ ρ hsub hne e he0 heS W hU hP
  have hsimple : IsSimpleRep ρ := isSimpleRep_of_addSubgroup hsub hne
  obtain ⟨θ, φ, hφe, hφ, hθφ⟩ := exists_om8_stated_transport he0 heS
  have hmemθ : ∀ (g : CFSG.StandardType.Triality.Om8 K),
      (g : GL (Fin (2 * 4)) K) ∈
        rootGroupGL (coordinateQuadPlus 4 K) (CFSG.StandardType.AutOm.pvec 1 true) →
      (θ g).val ∈ rootGroupGL (quadPlus 4 K) e := by
    intro g hg
    have hmem := mem_rootGroupGL_of_intertwine (Q := coordinateQuadPlus 4 K)
      (Q' := quadPlus 4 K) φ hφ (hθφ g) hg
    rwa [hφe] at hmem
  have hP1 : ∀ (g : CFSG.StandardType.Triality.Om8 K),
      (g : GL (Fin (2 * 4)) K) ∈
        lineStabilizer (coordinateQuadPlus 4 K) (CFSG.StandardType.AutOm.pvec 1 true) →
      ∃ c : K, ((θ g).val : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e = c • e := by
    intro g hg
    have hmem : (θ g).val ∈
        lineStabilizer (quadPlus 4 K) (φ (CFSG.StandardType.AutOm.pvec 1 true)) :=
      mem_lineStabilizer_of_intertwine (Q := coordinateQuadPlus 4 K)
        (Q' := quadPlus 4 K) φ hφ (hθφ g) hg
    rw [hφe] at hmem
    exact ((mem_lineStabilizer_iff (quadPlus 4 K)).mp hmem).2
  let ρ' : Representation K (CFSG.StandardType.Triality.Om8 K) Y := ρ.comp θ.toMonoidHom
  have hsimple' : IsSimpleRep ρ' := by
    rw [isSimpleRep_comp_iff ρ θ.surjective]
    exact hsimple
  rcases h K Y ρ' hsimple' W
    (fun g hg y hyW =>
      hU (θ g) ((sec7_siegel_iff_rootGroupGL heS he0 (θ g)).mpr (hmemθ g hg)) y hyW)
    (fun g hg y hyW => hP (θ g) (hP1 g hg) y hyW) with hbot | htop
  · exact Or.inl hbot
  · refine Or.inr fun y hy => htop y fun g hg =>
      hy (θ g) ((sec7_siegel_iff_rootGroupGL heS he0 (θ g)).mpr (hmemθ g hg))

theorem smithOmegaPlusEight_holds :
    SmithOmegaPlusEightStatement :=
  smithOmegaPlusEight_of_om8 fun _ _ _ _ _ _ _ _ hρ _ hX hXP =>
    CFSG.StandardType.TriBridge.eq_bot_or_fixed_le_of_rootGroupGL hρ hX hXP

end CFSG.RankThree.GF2n.Stroth80
