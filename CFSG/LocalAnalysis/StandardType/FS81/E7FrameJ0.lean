module

public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNative
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT
open CFSG.Timmesfeld
open scoped MatrixGroups

private theorem sl2_exists_inv : ∀ x : SL(2, ZMod 2), x ^ 3 = 1 → x ≠ 1 →
    ∃ t : SL(2, ZMod 2), t * x * t⁻¹ = x⁻¹ := by
  decide +kernel

private theorem sl2_conj : ∀ x : SL(2, ZMod 2), x ^ 3 = 1 → ∀ g : SL(2, ZMod 2),
    g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  decide +kernel

private theorem sl2_center : ∀ g : SL(2, ZMod 2), (∀ h : SL(2, ZMod 2), g * h = h * g) → g = 1 := by
  decide +kernel

private theorem sl2_closure : ∀ x z : SL(2, ZMod 2), x ≠ 1 → z ^ 3 = 1 → z ≠ 1 →
    ∃ g₁ g₂ : SL(2, ZMod 2), z = g₁ * x * g₁⁻¹ * (g₂ * x * g₂⁻¹) ∨ z = g₁ * x * g₁⁻¹ := by
  decide +kernel

private theorem sl2_eq_of_pow_three : ∀ x y : SL(2, ZMod 2), x ^ 3 = 1 → x ≠ 1 → y ^ 3 = 1 →
    y = 1 ∨ y = x ∨ y = x⁻¹ := by
  decide +kernel

private theorem sl2_eq_of_inv : ∀ x t y : SL(2, ZMod 2), x ^ 3 = 1 → x ≠ 1 →
    t * x * t⁻¹ = x⁻¹ → y = 1 ∨ y = x ∨ y = x⁻¹ ∨ y = t ∨ y = t * x ∨ y = t * x⁻¹ := by
  decide +kernel

private theorem pow_three_of_orderOf {X : Type} [Group X] {x : X} (hx : orderOf x = 3) :
    x ^ 3 = 1 ∧ x ≠ 1 := by
  refine ⟨hx ▸ pow_orderOf_eq_one x, fun h => ?_⟩
  rw [h, orderOf_one] at hx
  exact absurd hx (by decide)


theorem jn0_equiv (hF : E7NatFrame) : Nonempty (↥(Jn 0) ≃* SL(2, ZMod 2)) := by
  obtain ⟨W, hW⟩ := hF.2.2.1 0 2 (by decide)
  exact (CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_equiv hW).1

theorem jn0_exists_inv (hF : E7NatFrame) {z : ModGL .E7 (ZMod 2)} (hz : z ∈ Jn 0)
    (hz3 : orderOf z = 3) : ∃ t ∈ Jn 0, t * z * t⁻¹ = z⁻¹ := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h3 : orderOf (e ⟨z, hz⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  obtain ⟨h1, hne⟩ := pow_three_of_orderOf h3
  obtain ⟨t, ht⟩ := sl2_exists_inv _ h1 hne
  refine ⟨(e.symm t : ↥(Jn 0)), (e.symm t).2, ?_⟩
  have h := congrArg (fun y => ((e.symm y : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) ht
  simpa using h

theorem jn0_conj_mem (hF : E7NatFrame) {z : ModGL .E7 (ZMod 2)} (hz : z ∈ Jn 0)
    (hz3 : orderOf z = 3) {g : ModGL .E7 (ZMod 2)} (hg : g ∈ Jn 0) :
    g * z * g⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h3 : orderOf (e ⟨z, hz⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  obtain ⟨h1, -⟩ := pow_three_of_orderOf h3
  rcases sl2_conj _ h1 (e ⟨g, hg⟩) with h | h
  · have h' := congrArg (fun y => ((e.symm y : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h'
    rw [h']
    exact Subgroup.mem_zpowers z
  · have h' := congrArg (fun y => ((e.symm y : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h'
    rw [h']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)

theorem jn0_mem_zpowers (hF : E7NatFrame) {z : ModGL .E7 (ZMod 2)} (hz : z ∈ Jn 0)
    (hz3 : orderOf z = 3) {y : ModGL .E7 (ZMod 2)} (hy : y ∈ Jn 0) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers z := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h3 : orderOf (e ⟨z, hz⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  obtain ⟨h1, hne⟩ := pow_three_of_orderOf h3
  have hy3' : (e ⟨y, hy⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨y, hy⟩ : ↥(Jn 0)) ^ 3 = 1 from Subtype.ext (by simpa using hy3),
      map_one]
  rcases sl2_eq_of_pow_three _ _ h1 hne hy3' with h | h | h
  · have h' := congrArg (fun w => ((e.symm w : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [MulEquiv.symm_apply_apply, map_one, Subgroup.coe_one] at h'
    rw [h']
    exact Subgroup.one_mem _
  · have h' := congrArg (fun w => ((e.symm w : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [MulEquiv.symm_apply_apply] at h'
    rw [h']
    exact Subgroup.mem_zpowers z
  · have h' := congrArg (fun w => ((e.symm w : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [MulEquiv.symm_apply_apply, map_inv, Subgroup.coe_inv] at h'
    rw [h']
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)

theorem jn0_eq_one_of_central (hF : E7NatFrame) {g : ModGL .E7 (ZMod 2)} (hg : g ∈ Jn 0)
    (hc : ∀ h ∈ Jn 0, g * h = h * g) : g = 1 := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h1 : e ⟨g, hg⟩ = 1 := by
    refine sl2_center _ fun h => ?_
    have hh := hc _ (e.symm h).2
    have : (⟨g, hg⟩ : ↥(Jn 0)) * e.symm h = e.symm h * ⟨g, hg⟩ := Subtype.ext hh
    simpa using congrArg e this
  have h2 : (⟨g, hg⟩ : ↥(Jn 0)) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem jn0_mem_of_ne_one (hF : E7NatFrame) {z : ModGL .E7 (ZMod 2)} (hz : z ∈ Jn 0)
    (hz3 : orderOf z = 3) {x : ModGL .E7 (ZMod 2)} (hx : x ∈ Jn 0) (hx1 : x ≠ 1) :
    ∃ g₁ ∈ Jn 0, ∃ g₂ ∈ Jn 0, z = g₁ * x * g₁⁻¹ * (g₂ * x * g₂⁻¹) ∨ z = g₁ * x * g₁⁻¹ := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h3 : orderOf (e ⟨z, hz⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  obtain ⟨h1, hne⟩ := pow_three_of_orderOf h3
  have hx' : e ⟨x, hx⟩ ≠ 1 := fun h => hx1 (by
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this)
  obtain ⟨g₁, g₂, h⟩ := sl2_closure _ _ hx' h1 hne
  refine ⟨(e.symm g₁ : ↥(Jn 0)), (e.symm g₁).2, (e.symm g₂ : ↥(Jn 0)), (e.symm g₂).2, ?_⟩
  rcases h with h | h
  · left
    have h' := congrArg (fun y => ((e.symm y : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simpa using h'
  · right
    have h' := congrArg (fun y => ((e.symm y : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simpa using h'

theorem jn0_eq_of_inv (hF : E7NatFrame) {z : ModGL .E7 (ZMod 2)} (hz : z ∈ Jn 0)
    (hz3 : orderOf z = 3) {t : ModGL .E7 (ZMod 2)} (ht : t ∈ Jn 0) (htz : t * z * t⁻¹ = z⁻¹)
    {y : ModGL .E7 (ZMod 2)} (hy : y ∈ Jn 0) :
    y = 1 ∨ y = z ∨ y = z⁻¹ ∨ y = t ∨ y = t * z ∨ y = t * z⁻¹ := by
  obtain ⟨e⟩ := jn0_equiv hF
  have h3 : orderOf (e ⟨z, hz⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz3]
  obtain ⟨h1, hne⟩ := pow_three_of_orderOf h3
  have hte : e ⟨t, ht⟩ * e ⟨z, hz⟩ * (e ⟨t, ht⟩)⁻¹ = (e ⟨z, hz⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    exact congrArg e (Subtype.ext (by simpa using htz))
  rcases sl2_eq_of_inv _ _ (e ⟨y, hy⟩) h1 hne hte with h | h | h | h | h | h <;>
  · have h' := congrArg (fun w => ((e.symm w : ↥(Jn 0)) : ModGL .E7 (ZMod 2))) h
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv, map_one, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_one] at h'
    simp [h']

theorem m0_eq_one_of_central (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent)
    {g : ModGL .E7 (ZMod 2)} (hg : g ∈ M0) (hc : ∀ h ∈ M0, g * h = h * g) : g = 1 := by
  have hsimple : IsSimpleGroup ↥M0 := hC.2.2.1
  have hnc : ¬ ∀ x ∈ M0, ∀ y ∈ M0, x * y = y * x := by
    intro hall
    obtain ⟨W, hW⟩ := hF.2.2.1 1 3 (by decide)
    apply CFSG.ClassicalInvolution.RouteD.not_commutes_of_linearBlockStandardPair hW
    intro x hx y hy
    exact hall x (hH.2.2.2.2.1 1 (by decide) (by decide) hx) y
      (hH.2.2.2.2.1 3 (by decide) (by decide) hy)
  have hZ : Subgroup.center ↥M0 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥M0) with h | h
    · exact h
    · exfalso
      apply hnc
      intro x hx y hy
      have hxc : (⟨x, hx⟩ : ↥M0) ∈ Subgroup.center ↥M0 := h ▸ Subgroup.mem_top _
      have := Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
  have hgc : (⟨g, hg⟩ : ↥M0) ∈ Subgroup.center ↥M0 := by
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hc h h.2).symm
  rw [hZ, Subgroup.mem_bot] at hgc
  exact congrArg Subtype.val hgc

end CFSG.StandardType.FrameRoute.FS81.E7Frame
