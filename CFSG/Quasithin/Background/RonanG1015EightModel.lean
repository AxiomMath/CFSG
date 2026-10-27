module

public import CFSG.LieType.ChevTwo.OrthogonalAutEight
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Open
open CFSG.LieType.ChevTwo
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
open CFSG.ClassicalInvolution.ModelFacts.OrthAut
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LieType.Universal.Spin
open scoped Pointwise

local notation "Q8" => StatedQuadPlus 4 (ZMod 2)
local notation "Ω8" => StatedOmega (StatedQuadPlus 4 (ZMod 2))
local notation "P8" => StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))

@[expose] noncomputable def projEquiv8 : Ω8 ≃* P8 :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk',
      CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf],
    QuotientGroup.mk'_surjective _⟩

theorem projEquiv8_apply (x : Ω8) : projEquiv8 x = QuotientGroup.mk' _ x := rfl

theorem zmodTwo_ringEquiv_apply' (σ : ZMod 2 ≃+* ZMod 2) (x : ZMod 2) : σ x = x := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem inducedByIso_of_smul_eq' (α : MulAut Ω8)
    (hα : MulAut.congr projEquiv8 α • statedPointFamily (coe_quadPlus 4 (ZMod 2)) =
      statedPointFamily (coe_quadPlus 4 (ZMod 2))) :
    InducedByIso Q8 α := by
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 1 := ⟨Nat.prime_two, le_rfl, le_rfl⟩
  have h : StatedClassicalModel P8 .POmegaPlus 4 2 1 :=
    ⟨hadm, ZMod 2, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hmem := congr_mem_pointFamilyAut _ hα
  rw [coordinate_plus_family_eq_matrixImage h (ZMod 2) hK (MulEquiv.refl _)] at hmem
  obtain ⟨A, σ, μ, hQ, hx⟩ := exists_similarity_of_mem_image (plusIndexEquiv 4)
    (quadPlus 4 (ZMod 2)) (coe_quadPlus 4 (ZMod 2)) _ hmem
  have hσ : ∀ x, σ x = x := zmodTwo_ringEquiv_apply' σ
  have hμ : μ = 1 := Subsingleton.elim _ _
  have hgl : ∀ g : GL (Fin 4 ⊕ Fin 4) (ZMod 2),
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv _ σ g = g := by
    intro g
    apply Units.ext
    ext i j
    exact hσ _
  refine ⟨A, fun v => ?_, fun x => ?_⟩
  · have := hQ v
    simp only [hσ, hμ, Units.val_one, one_mul, coe_quadPlus] at this
    exact this
  · obtain ⟨y, hy, hxy⟩ := hx x
    have h0 : (MulAut.congr projEquiv8 α) (QuotientGroup.mk x) = projEquiv8 (α x) := by
      change (MulAut.congr projEquiv8 α) (projEquiv8 x) = _
      simp [MulAut.congr_apply]
    have h1 : α x = y := projEquiv8.injective (h0.symm.trans hxy)
    rw [h1, hy, hgl]

theorem g12_eq_zero_or_one' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem points_ext_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (a b : CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.Points Q) : a = b ↔ a.val = b.val :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem mem_pointStabilizer_iff {w : Fin 4 ⊕ Fin 4 → ZMod 2} (hw : w ≠ 0)
    (hQw : quadPlus 4 (ZMod 2) w = 0) (x : Ω8) :
    projEquiv8 x ∈ statedPointStabilizer (coe_quadPlus 4 (ZMod 2)) (CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.pointMk w hw hQw) ↔
      ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec
        w = w := by
  rw [mem_statedPointStabilizer_iff, projEquiv8_apply, points_ext_iff,
    CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.statedPointAction_mk_submodule, CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.pointMk_submodule, Submodule.map_span, Set.image_singleton]
  simp only [LinearEquiv.coe_coe, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  constructor
  · intro h
    have hmem : ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4)
        (ZMod 2)).mulVec w ∈ Submodule.span (ZMod 2) {w} := by
      rw [← h]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases g12_eq_zero_or_one' c with rfl | rfl
    · exfalso
      rw [zero_smul] at hc
      apply hw
      have h0 := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2)
        (x : GL (Fin 4 ⊕ Fin 4) (ZMod 2))).map_eq_zero_iff.1 (by
          rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]; exact hc.symm)
      exact h0
    · rw [one_smul] at hc
      exact hc.symm
  · intro h
    rw [h]

theorem inducedByIso_of_fix (α : MulAut Ω8) {w : Fin 4 ⊕ Fin 4 → ZMod 2} (hw : w ≠ 0)
    (hQw : quadPlus 4 (ZMod 2) w = 0)
    (h1 : ∀ x : Ω8, ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec w = w →
        (((α x : Ω8) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec w = w)
    (h2 : ∀ x : Ω8, (((α x : Ω8) : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec w = w →
        ((x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)).mulVec w = w) :
    InducedByIso Q8 α := by
  apply inducedByIso_of_smul_eq'
  set L := CFSG.ComponentClassification.CatalogueBOrthogonalPointAction.pointMk
    (Q := quadPlus 4 (ZMod 2)) w hw hQw with hL
  set H := statedPointStabilizer (coe_quadPlus 4 (ZMod 2)) L with hH
  have hF : statedPointFamily (coe_quadPlus 4 (ZMod 2)) = conjugacyFamily H :=
    ((stated_intrinsic (K := ZMod 2) (n := 4) (by norm_num)).2.2 L).1
  have hc : ∀ y : Ω8, (MulAut.congr projEquiv8 α) (projEquiv8 y) = projEquiv8 (α y) :=
    fun y => by simp [MulAut.congr_apply]
  have hHα : H.map (MulAut.congr projEquiv8 α).toMonoidHom = H := by
    ext p
    obtain ⟨x, rfl⟩ := projEquiv8.surjective p
    constructor
    · rintro ⟨p', hp', hp'x⟩
      obtain ⟨y, rfl⟩ := projEquiv8.surjective p'
      have hyx : α y = x := projEquiv8.injective ((hc y).symm.trans hp'x)
      have hy := (mem_pointStabilizer_iff hw hQw y).1 hp'
      rw [← hyx]
      exact (mem_pointStabilizer_iff hw hQw (α y)).2 (h1 y hy)
    · intro hx
      have hx' := (mem_pointStabilizer_iff hw hQw x).1 hx
      refine ⟨projEquiv8 (α.symm x), ?_, ?_⟩
      · refine (mem_pointStabilizer_iff hw hQw (α.symm x)).2 (h2 _ ?_)
        rw [MulEquiv.apply_symm_apply]
        exact hx'
      · show (MulAut.congr projEquiv8 α) (projEquiv8 (α.symm x)) = projEquiv8 x
        rw [hc, MulEquiv.apply_symm_apply]
  rw [hF, conjugacyFamily_covariance, hHα]

end RonanG1015

end CFSG.Quasithin
