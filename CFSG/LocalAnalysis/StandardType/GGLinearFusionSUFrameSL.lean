module

public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.StandardType.GGSLBstarFrame
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.SeitzReduction.LinearPilot Matrix

namespace LinFrameSL

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem mem_ggFrameTorus_of_frameDiag {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {A₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) F} {b : G}
    (h : SLRep.GGFrameDiag (SLRep.ggFrame ψ A₀) b) :
    b ∈ LinFusion.ggFrameTorus F ψ (Matrix.SpecialLinearGroup.toGL A₀)⁻¹ := by
  obtain ⟨D, t, hD, hb⟩ := h
  obtain ⟨d, hd⟩ := LinTorus.exists_eq_diagGL (M := D) fun i j hij => by
    rw [hD, diagonal_apply_ne _ hij]
  refine ⟨d, LinFusion.mem_ggInducedPairs.mpr fun u => ?_⟩
  have h1 := hb (A₀⁻¹ * u * A₀)
  rw [SLRep.ggFrame_apply, SLRep.ggFrame_apply,
    show A₀ * (A₀⁻¹ * u * A₀) * A₀⁻¹ = u by group] at h1
  rw [h1]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [RootPlaneA.toGL_conjSL, LinFusion.ggFrameDiag, inv_inv, map_mul, map_mul, map_inv,
    ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul,
    map_inv, hd]
  group

theorem ggFrameBlock_eq_bot_of_card_le_one (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) {I : Finset (Fin (m + 1))} (hI : I.card ≤ 1) :
    LinFusion.ggFrameBlock F ψ P I = ⊥ := by
  rw [LinFusion.ggFrameBlock, LinFusion.blockSpecialLinear_eq_bot_of_card_le_one hI,
    Subgroup.map_bot]

@[expose] def rootHom {i j : Fin (m + 1)} (hij : i ≠ j) :
    Multiplicative F →* Matrix.SpecialLinearGroup (Fin (m + 1)) F where
  toFun c := Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd c)
  map_one' := by
    rw [toAdd_one, Matrix.SpecialLinearGroup.transvection_coeff_zero]
  map_mul' a b := by
    rw [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add]

theorem rootHom_apply {i j : Fin (m + 1)} (hij : i ≠ j) (c : Multiplicative F) :
    rootHom hij c = Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd c) :=
  rfl

variable (F) in
@[expose] noncomputable def rootSub (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) {i j : Fin (m + 1)} (hij : i ≠ j) : Subgroup G :=
  (rootHom hij).range.map (ψ.comp (InnerDiagA.conjSL P⁻¹))

theorem mem_rootSub {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} {i j : Fin (m + 1)} {hij : i ≠ j} {g : G} :
    g ∈ rootSub F ψ P hij ↔
      ∃ c : F, ψ (InnerDiagA.conjSL P⁻¹ (Matrix.SpecialLinearGroup.transvection hij c)) = g := by
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨Multiplicative.toAdd c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨Multiplicative.ofAdd c, rfl⟩, rfl⟩

theorem isPGroup_rootSub [CharP F 2] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) {i j : Fin (m + 1)} (hij : i ≠ j) :
    IsPGroup 2 (rootSub F ψ P hij) := by
  rintro ⟨g, hg⟩
  obtain ⟨c, rfl⟩ := mem_rootSub.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, sq, ← map_mul, ← map_mul,
    ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one, map_one]

theorem rootSub_ne_bot {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (P : GL (Fin (m + 1)) F) {i j : Fin (m + 1)} (hij : i ≠ j) : rootSub F ψ P hij ≠ ⊥ := by
  intro hbot
  have h1 : ψ (InnerDiagA.conjSL P⁻¹ (Matrix.SpecialLinearGroup.transvection hij (1 : F))) ∈
      rootSub F ψ P hij := mem_rootSub.mpr ⟨1, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈
      (ψ.comp (InnerDiagA.conjSL P⁻¹)).ker := h1
  have h3 := (Matrix.SpecialLinearGroup.transvection_mem_center_iff hij (1 : F)).mp
    (LinFusion.ker_comp_conjSL_le_center hker P⁻¹ h2)
  exact one_ne_zero h3

theorem rootSub_le_ggFrameBlock (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (P : GL (Fin (m + 1)) F) {I : Finset (Fin (m + 1))} {i j : Fin (m + 1)} (hij : i ≠ j)
    (hi : i ∈ I) (hj : j ∈ I) : rootSub F ψ P hij ≤ LinFusion.ggFrameBlock F ψ P I := by
  intro g hg
  obtain ⟨c, rfl⟩ := mem_rootSub.mp hg
  exact Subgroup.mem_map_of_mem _ (transvection_mem_blockSpecialLinear hij hi hj c)

theorem conj_mem_rootSub {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} {i j : Fin (m + 1)} {hij : i ≠ j} {y : G}
    (hy : y ∈ LinFusion.ggFrameTorus F ψ P) {g : G} (hg : g ∈ rootSub F ψ P hij) :
    y * g * y⁻¹ ∈ rootSub F ψ P hij := by
  obtain ⟨d, hd⟩ := hy
  obtain ⟨c, rfl⟩ := mem_rootSub.mp hg
  have h1 := LinFusion.mem_ggInducedPairs.mp (LinTorus.mem_ggInducedPairs_frame hd)
    (Matrix.SpecialLinearGroup.transvection hij c)
  simp only [MonoidHom.comp_apply] at h1
  rw [h1, InnerDiagA.conjSL_diagGL_transvection]
  exact mem_rootSub.mpr ⟨_, rfl⟩

theorem le_normalizer_rootSub {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {P : GL (Fin (m + 1)) F} {i j : Fin (m + 1)} (hij : i ≠ j) :
    LinFusion.ggFrameTorus F ψ P ≤ Subgroup.normalizer (rootSub F ψ P hij : Set G) := by
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun g => ⟨conj_mem_rootSub hy, fun hg => ?_⟩
  have h := conj_mem_rootSub (Subgroup.inv_mem _ hy) hg
  rwa [inv_inv, show y⁻¹ * (y * g * y⁻¹) * y = g by group] at h

end LinFrameSL

section Inputs

theorem ggLinearFrameEqInput_holds : GGLinearFrameEqInput := by
  intro G _ _ p B Bs x L D J m f ψ hctx s1 hp
  obtain ⟨A₀, hA₀⟩ := ggSLBstarFrameInput_holds G p B Bs x L D J m f ψ hctx s1 hp
  set P : GL (Fin (m + 1)) (GaloisField 2 f) := (Matrix.SpecialLinearGroup.toGL A₀)⁻¹ with hP
  have hBT : Bs ≤ LinFusion.ggFrameTorus (GaloisField 2 f) ψ P := fun b hb =>
    LinFrameSL.mem_ggFrameTorus_of_frameDiag (hA₀ b hb)
  have hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hctx.range_eq]
    exact hctx.j_isComponentOf_inf
  obtain ⟨I₀, hJI, -⟩ := LinSemisimple.exists_eq_ggFrameBlock_of_le_ggFrameTorus hker P
    (hctx.d_le_bstar.trans hBT) hJ
  refine ⟨P, I₀, hBT, le_antisymm ?_ (le_inf hctx.d_le_bstar (hJI ▸ hctx.le_centralizer_J))⟩
  have hI₀ : 2 ≤ I₀.card := by
    by_contra hlt
    have hbot : J = ⊥ := by
      rw [hJI]
      exact LinFrameSL.ggFrameBlock_eq_bot_of_card_le_one ψ P (by omega)
    exact LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2 fun a ha b hb => by
      rw [hbot, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < I₀.card)
  rw [← hJI]
  exact ggStdSubBstarCentralizer_of_twoSubgroup hctx.config
    ⟨LinFrameSL.rootSub (GaloisField 2 f) ψ P hij, LinFrameSL.rootSub_ne_bot hker P hij,
      LinFrameSL.isPGroup_rootSub ψ P hij,
      hJI ▸ LinFrameSL.rootSub_le_ggFrameBlock ψ P hij hi hj,
      (hctx.2.1.1.trans hBT).trans (LinFrameSL.le_normalizer_rootSub hij)⟩

theorem ggStepTwoLinearFusionInput_of_unitaryHalf (hU : GGStepTwoUnitaryFusionInput) :
    GGStepTwoLinearFusionInput :=
  ggStepTwoLinearFusionInput_of_frameEqInput ggLinearFrameEqInput_holds hU

end Inputs

end CFSG.StandardType
