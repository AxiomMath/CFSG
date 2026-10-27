module

public import CFSG.RankThree.PartOne.TCX.LayerEngine
public import CFSG.RankThree.PartOne.KLC.Transport

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KLC
open CFSG.RankThree.PartOne.TCX.F4 (LayerClaimsF4)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Blueprint (LieModel)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

variable {T G : Type} [Group T] [Group G]

theorem mem_map_symm_iff (φ : T ≃* G) (D' : Subgroup G) {g : T} :
    g ∈ D'.map φ.symm.toMonoidHom ↔ φ g ∈ D' := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem map_map_symm (φ : T ≃* G) (X : Subgroup T) :
    (X.map φ.toMonoidHom).map φ.symm.toMonoidHom = X := by
  ext g
  rw [mem_map_symm_iff, Subgroup.mem_map_equiv]
  simp

theorem layerClaims_of_mulEquiv {p : ℕ} (φ : T ≃* G) {αT : MulAut T} {αG : MulAut G}
    (hαφ : ∀ t, αG (φ t) = φ (αT t)) {D' : Subgroup G} (h : LayerClaimsF4 p αG D') :
    LayerClaimsF4 p αT (D'.map φ.symm.toMonoidHom) := by
  obtain ⟨hnon, ⟨t', n', f', hf', hmodel⟩, t₁, ht₁, hα₁, t₂, ht₂, hα₂, ho₁, ho₂, hnc⟩ := h
  refine ⟨fun e he hcon => ?_, ?_, φ.symm t₁, (mem_map_symm_iff φ D').2 (by simpa using ht₁), ?_,
    φ.symm t₂, (mem_map_symm_iff φ D').2 (by simpa using ht₂), ?_, ?_, ?_, ?_⟩
  ·
    have he' : φ e ∈ D' := (mem_map_symm_iff φ D').1 he
    apply hnon (φ e) he'
    intro q hq
    have hg : φ.symm q ∈ D'.map φ.symm.toMonoidHom := (mem_map_symm_iff φ D').2 (by simpa using hq)
    have h1 := hcon _ hg
    have h2 := hαφ (φ.symm q)
    rw [MulEquiv.apply_symm_apply] at h2
    rw [h2, h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  ·
    let e₁ : ↥(D'.map φ.symm.toMonoidHom) ≃* ↥D' :=
      (Subgroup.equivMapOfInjective D' φ.symm.toMonoidHom φ.symm.injective).symm
    let e₃ : ↥(D'.map φ.symm.toMonoidHom) ⧸ Subgroup.center ↥(D'.map φ.symm.toMonoidHom) ≃*
        ↥D' ⧸ Subgroup.center ↥D' :=
      QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
    exact ⟨t', n', f', hf', lieModel_of_mulEquiv e₃.symm hmodel⟩
  · apply φ.injective
    rw [← hαφ, MulEquiv.apply_symm_apply]
    exact hα₁
  · apply φ.injective
    rw [← hαφ, MulEquiv.apply_symm_apply]
    exact hα₂
  · obtain ⟨k, hk⟩ := ho₁
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
  · obtain ⟨k, hk⟩ := ho₂
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
  · intro hcomm
    apply hnc
    have := congrArg φ hcomm
    simpa [map_mul] using this

theorem singleLayerData_of_mulEquiv {p : ℕ} (φ : T ≃* G) {αT : MulAut T} {αG : MulAut G}
    (hαφ : ∀ t, αG (φ t) = φ (αT t)) {X : Subgroup T}
    (h : SingleLayerData p αG (X.map φ.toMonoidHom)) : SingleLayerData p αT X := by
  obtain ⟨D', hD', hst, huniq, hfix, hclaims⟩ := h
  refine ⟨D'.map φ.symm.toMonoidHom, ?_, fun g hg => ?_, fun D₂ hD₂ => ?_,
    fun g hg hαg hgo => ?_, layerClaims_of_mulEquiv φ hαφ hclaims⟩
  · have := isComponentOf_map_mulEquiv' φ.symm hD'
    rwa [map_map_symm] at this
  · rw [mem_map_symm_iff] at hg ⊢
    have := hst _ hg
    rwa [hαφ] at this
  · have h1 := isComponentOf_map_mulEquiv' φ hD₂
    have h2 := huniq _ h1
    have h3 : (D₂.map φ.toMonoidHom).map φ.symm.toMonoidHom = D'.map φ.symm.toMonoidHom := by
      rw [h2]
    rwa [map_map_symm] at h3
  · rw [mem_map_symm_iff]
    refine hfix (φ g) ⟨g, hg, rfl⟩ (by rw [hαφ, hαg]) ?_
    obtain ⟨k, hk⟩ := hgo
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩

end CFSG.RankThree.PartOne.TCX
