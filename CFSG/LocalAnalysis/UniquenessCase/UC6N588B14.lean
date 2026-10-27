module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B13
public import CFSG.RankThree.PartOne.KF.LayerGen
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

namespace Mz614

namespace A10Setup

variable {G : Type} [Group G] [Finite G] {m : Mz614 G} (D : A10Setup m)

@[expose] noncomputable def CKZ : Subgroup ↥D.Ka :=
  centralizer ((m.Z.subgroupOf D.Ka : Subgroup ↥D.Ka) : Set ↥D.Ka)

@[expose] noncomputable def evC : ↥D.CKZ →* G := D.Ka.subtype.comp D.CKZ.subtype

theorem evC_injective : Function.Injective D.evC :=
  D.Ka.subtype_injective.comp D.CKZ.subtype_injective

theorem mem_CKZ_iff {x : ↥D.Ka} : x ∈ D.CKZ ↔ (x : G) ∈ m.H := by
  rw [CKZ, mem_centralizer_iff]
  constructor
  · intro h
    refine mem_centralizer_iff.2 fun z hz => ?_
    have := h ⟨z, D.Z_le_Ka hz⟩ (mem_subgroupOf.2 hz)
    exact congrArg Subtype.val this
  · intro h z hz
    exact Subtype.ext (mem_centralizer_iff.1 h _ (mem_subgroupOf.1 hz))

theorem evC_mem_H (y : ↥D.CKZ) : D.evC y ∈ m.H := D.mem_CKZ_iff.1 y.2

theorem evC_mem_Ka (y : ↥D.CKZ) : D.evC y ∈ D.Ka := (y : ↥D.Ka).2

@[expose] noncomputable def layerSub : Subgroup ↥D.CKZ := m.L.comap D.evC

theorem layerSub_normal : D.layerSub.Normal := by
  refine ⟨fun n hn y => ?_⟩
  show D.evC (y * n * y⁻¹) ∈ m.L
  rw [map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.1 (m.H_le_normalizer_L (D.evC_mem_H y)) _).1 hn

theorem map_evC_layerSub : D.layerSub.map D.evC = (altA T6).map D.ι := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨σ, hσ⟩ := D.exists_ι (show D.evC y ∈ m.L from hy)
    refine ⟨σ, (D.ι_mem_Ka_iff σ).1 ?_, hσ⟩
    rw [hσ]
    exact D.evC_mem_Ka y
  · rintro ⟨σ, hσ, rfl⟩
    have hK : D.ι σ ∈ D.Ka := (D.ι_mem_Ka_iff σ).2 hσ
    have hC : (⟨D.ι σ, hK⟩ : ↥D.Ka) ∈ D.CKZ := D.mem_CKZ_iff.2 (m.L_le_H (D.ι_mem_L σ))
    exact ⟨⟨⟨D.ι σ, hK⟩, hC⟩, D.ι_mem_L σ, rfl⟩

noncomputable def layerSubEquiv : ↥D.layerSub ≃* ↥(altA T6) :=
  ((D.layerSub.equivMapOfInjective D.evC D.evC_injective).trans
    (MulEquiv.subgroupCongr D.map_evC_layerSub)).trans
    ((altA T6).equivMapOfInjective D.ι D.ι_injective).symm

theorem isQuasisimple_layerSub : CFSG.IsQuasisimple ↥D.layerSub := by
  have hs : IsSimpleGroup ↥(altA T6) := isSimpleGroup_altA T6 (by rw [card_T6]; norm_num)
  have hs' : IsSimpleGroup ↥D.layerSub := D.layerSubEquiv.isSimpleGroup
  refine isQuasisimple_of_simple_uc6b hs' (x := D.layerSubEquiv.symm ⟨t₀, t₀_mem_T6⟩)
    (y := D.layerSubEquiv.symm ⟨a₁, a₁_mem_T6⟩) fun h => t₀_a₁_ne ?_
  have h' := congrArg (fun t => ((D.layerSubEquiv t : ↥(altA T6)) : A10)) h
  simpa using h'

@[expose] noncomputable def inclCHL : ↥(centralizer (m.L : Set G) ⊓ m.H) →* ↥D.CKZ :=
  MonoidHom.codRestrict
    (MonoidHom.codRestrict (centralizer (m.L : Set G) ⊓ m.H).subtype D.Ka
      fun c => D.centralizer_L_le_Ka c.2.1)
    D.CKZ fun c => D.mem_CKZ_iff.2 c.2.2

theorem evC_inclCHL (c : ↥(centralizer (m.L : Set G) ⊓ m.H)) : D.evC (D.inclCHL c) = c := rfl

noncomputable def chiC : ↥D.CKZ →* ℤˣ :=
  D.chi.comp (D.evC.codRestrict (normalizer (m.L : Set G))
    fun y => m.H_le_normalizer_L (D.evC_mem_H y))

include D in
theorem isSolvable_quotient_layerSub (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (h620 : m.C620) (hr : m.r = 5) {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L)
    (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) :
    haveI := D.layerSub_normal
    Group.IsSolvable (↥D.CKZ ⧸ D.layerSub) := by
  haveI := D.layerSub_normal
  haveI := D.isSolvable_CHL h69 h620 hr hw₁ hw₂
  have hN : D.layerSub ≤ D.chiC.ker := fun n hn =>
    D.chi_of_mem_L (show D.evC n ∈ m.L from hn) _
  let g : ↥D.CKZ ⧸ D.layerSub →* ℤˣ := QuotientGroup.lift D.layerSub D.chiC hN
  let f : ↥(centralizer (m.L : Set G) ⊓ m.H) →* ↥D.CKZ ⧸ D.layerSub :=
    (QuotientGroup.mk' D.layerSub).comp D.inclCHL
  refine Group.isSolvable_of_ker_le_range f g fun q hq => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hy : D.chiC y = 1 := hq
  obtain ⟨ℓ, hℓL, hc⟩ := D.exists_mem_centralizer_of_chi_eq_one hy
  have hyH := D.evC_mem_H y
  have hcH : ℓ⁻¹ * D.evC y ∈ m.H := mul_mem (inv_mem (m.L_le_H hℓL)) hyH
  refine ⟨⟨ℓ⁻¹ * D.evC y, hc, hcH⟩, ?_⟩
  show (QuotientGroup.mk (D.inclCHL ⟨ℓ⁻¹ * D.evC y, hc, hcH⟩) : ↥D.CKZ ⧸ D.layerSub) =
    QuotientGroup.mk y
  rw [QuotientGroup.eq]
  show D.evC ((D.inclCHL ⟨ℓ⁻¹ * D.evC y, hc, hcH⟩)⁻¹ * y) ∈ m.L
  rw [map_mul, map_inv, D.evC_inclCHL]
  have hconj := (mem_normalizer_iff.1 (inv_mem (m.H_le_normalizer_L hyH)) ℓ).1 hℓL
  have e : (ℓ⁻¹ * D.evC y)⁻¹ * D.evC y = ((D.evC y)⁻¹ * ℓ * (D.evC y)⁻¹⁻¹) := by group
  rw [e]
  exact hconj

include D in
theorem isAlt_layer (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h620 : m.C620) (hr : m.r = 5)
    {w : G} (hw₁ : ∀ z ∈ m.Z, w * z * w⁻¹ ∈ m.L) (hw₂ : ∀ z ∈ m.Z, w⁻¹ * z * w ∈ m.L) :
    UC22.IsAlt ↥((genFittingLayer ↥(centralizer ((m.Z.subgroupOf D.Ka : Subgroup ↥D.Ka) :
      Set ↥D.Ka))).map (centralizer ((m.Z.subgroupOf D.Ka : Subgroup ↥D.Ka) :
        Set ↥D.Ka)).subtype) 6 := by
  show UC22.IsAlt ↥((genFittingLayer ↥D.CKZ).map D.CKZ.subtype) 6
  haveI := D.layerSub_normal
  have hlayer : CFSG.layer ↥D.CKZ = D.layerSub :=
    CFSG.RankThree.PartOne.KFU.layer_eq_of_normal D.layerSub_normal D.isQuasisimple_layerSub
      (D.isSolvable_quotient_layerSub h69 h620 hr hw₁ hw₂)
  rw [CFSG.Adapters.genFittingLayer_eq_foundations, hlayer]
  exact ⟨((D.layerSub.equivMapOfInjective D.CKZ.subtype D.CKZ.subtype_injective).symm.trans
    D.layerSubEquiv).trans altA6Equiv⟩

end A10Setup

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
