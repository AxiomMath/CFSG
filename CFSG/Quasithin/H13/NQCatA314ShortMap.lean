module

public import CFSG.Quasithin.H13.NQCatA314ASL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Wreath

section Comap

variable {H G : Type*} [Group H] [Group G] (f : H →* G) (hf : Function.Injective f)

include hf

theorem IsShort2.of_map_injective {L : Subgroup H} (hL : IsShort2 (L.map f)) : IsShort2 L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have hQ := blockQ_map_injective f hf L
  have hU := blockU_map_injective f hf L
  have hZ := blockZ_map_injective f hf L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N _ hN
    have hNn : (N.map φ.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ φ.surjective
    let e : (↥L ⧸ N) ≃* (↥(L.map f) ⧸ N.map φ.toMonoidHom) := QuotientGroup.congr N _ φ rfl
    have h := h1 (N.map φ.toMonoidHom) (hN.of_equiv e)
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ N.map φ.toMonoidHom := h ▸ Subgroup.mem_top (φ x)
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← φ.injective hyx]
  · intro x hx
    obtain ⟨hxL, hxc⟩ := hx
    have h1x : f x ∈ L.map f ⊓ Subgroup.centralizer (pCoreOf 2 (L.map f) : Set G) := by
      refine ⟨⟨x, hxL, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro q hq
      have hq' : q ∈ (pCoreOf 2 L).map f := hQ ▸ hq
      obtain ⟨p, hp, rfl⟩ := hq'
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc p hp]
    have h2x := h2 h1x
    have h3x : f x ∈ (pCoreOf 2 L).map f := hQ ▸ h2x
    exact (Subgroup.mem_map_iff_mem hf).mp h3x
  · refine ⟨?_, fun x hx => ?_⟩
    · have hQc := map_inf_centralizer_map f hf (U := blockQ L) (L := blockQ L)
      have h3' := h3.1
      rw [hU, hQ, hQc] at h3'
      exact (Subgroup.map_le_map_iff_of_injective hf).mp h3'
    · have := h3.2 (f x) (hU ▸ ⟨x, hx, rfl⟩)
      apply hf
      rw [map_pow, this, map_one]
  · let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥(L.map f) ⧸ CFSG.pCore 2 ↥(L.map f)) :=
      QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
    rcases h4 with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mpr h)
    · exact Or.inr (by rw [Nat.card_congr e.toEquiv]; exact h)
  · rw [hZ, hU] at h5
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).mp h5.1, ?_⟩
    intro W hW1 hW2 hW3
    have hW3' : L.map f ≤ Subgroup.normalizer ((W.map f : Subgroup G) : Set G) := by
      rintro _ ⟨l, hl, rfl⟩
      exact Subgroup.le_normalizer_map f ⟨l, hW3 hl, rfl⟩
    rcases h5.2 (W.map f) (Subgroup.map_mono hW1) (Subgroup.map_mono hW2) hW3' with h | h
    · exact Or.inl (Subgroup.map_injective hf h)
    · exact Or.inr (Subgroup.map_injective hf h)

theorem IsLin2Type.of_map_injective {L : Subgroup H} {n : ℕ} (hL : IsLin2Type (L.map f) n) :
    IsLin2Type L n := by
  obtain ⟨F, _, _, hF, α, hα, hαk, β, hβ, hβk, hR⟩ := hL
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have hU := blockU_map_injective f hf L
  have hZ := blockZ_map_injective f hf L
  let ψ : ↥(blockU L) ≃* ↥(blockU (L.map f)) :=
    ((blockU L).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hU.symm)
  have hψ : ∀ u : ↥(blockU L), ((ψ u : ↥(blockU (L.map f))) : G) = f u := fun _ => rfl
  refine ⟨F, inferInstance, inferInstance, hF, α.comp φ.toMonoidHom, hα.comp φ.surjective, ?_,
    β.comp ψ.toMonoidHom, hβ.comp ψ.surjective, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk]
    rw [← CFSG.pCore_map_iso 2 φ]
    exact ⟨fun ⟨y, hy, hyx⟩ => by rwa [← φ.injective hyx], fun hx => ⟨x, hx, rfl⟩⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show ((ψ u : ↥(blockU (L.map f))) : G) ∈ blockZ (L.map f) ↔ (u : H) ∈ blockZ L
    rw [hψ, hZ]
    exact Subgroup.mem_map_iff_mem hf
  · intro ℓ u v huv
    refine hR (φ ℓ) (ψ u) (ψ v) ?_
    rw [hψ, hψ, huv, map_mul, map_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_inv]
    rfl

theorem IsLin2Type.map_of_injective' {L : Subgroup H} {n : ℕ} (hL : IsLin2Type L n) :
    IsLin2Type (L.map f) n := by
  obtain ⟨F, _, _, hF, α, hα, hαk, β, hβ, hβk, hR⟩ := hL
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have hU := blockU_map_injective f hf L
  have hZ := blockZ_map_injective f hf L
  let ψ : ↥(blockU L) ≃* ↥(blockU (L.map f)) :=
    ((blockU L).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hU.symm)
  have hψ : ∀ u : ↥(blockU L), ((ψ u : ↥(blockU (L.map f))) : G) = f u := fun _ => rfl
  have hψ' : ∀ u : ↥(blockU (L.map f)), f (ψ.symm u) = u := by
    intro u
    rw [← hψ, MulEquiv.apply_symm_apply]
  have hφ' : ∀ ℓ : ↥(L.map f), f (φ.symm ℓ) = ℓ := by
    intro ℓ
    change ((φ (φ.symm ℓ) : ↥(L.map f)) : G) = ℓ
    rw [MulEquiv.apply_symm_apply]
  refine ⟨F, inferInstance, inferInstance, hF, α.comp φ.symm.toMonoidHom,
    hα.comp φ.symm.surjective, ?_, β.comp ψ.symm.toMonoidHom, hβ.comp ψ.symm.surjective, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk,
      ← CFSG.pCore_map_iso 2 φ]
    constructor
    · intro hx
      exact ⟨φ.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hZ, ← hψ' u]
    exact (Subgroup.mem_map_iff_mem hf).symm
  · intro ℓ u v huv
    refine hR (φ.symm ℓ) (ψ.symm u) (ψ.symm v) (hf ?_)
    rw [hψ' v, huv, map_mul, map_mul, Subgroup.coe_inv, Subgroup.coe_inv, map_inv, hψ' u,
      hφ' ℓ]

end Comap

theorem isShort2_isLin2Type_of_mulEquiv {G : Type*} [Group G] {B : Subgroup G}
    (ψ : ↥K4 ≃* ↥B) : IsShort2 B ∧ IsLin2Type B 2 := by
  have htop : (⊤ : Subgroup ↥K4).map K4.subtype = K4 := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : IsShort2 (⊤ : Subgroup ↥K4) :=
    IsShort2.of_map_injective K4.subtype K4.subtype_injective (by rw [htop]; exact isShort2_K4)
  have h2 : IsLin2Type (⊤ : Subgroup ↥K4) 2 :=
    IsLin2Type.of_map_injective K4.subtype K4.subtype_injective
      (by rw [htop]; exact isLin2Type_K4)
  let g : ↥K4 →* G := B.subtype.comp ψ.toMonoidHom
  have hg : Function.Injective g := B.subtype_injective.comp ψ.injective
  have hB : (⊤ : Subgroup ↥K4).map g = B := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ ψ.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  exact ⟨hB ▸ IsShort2.map_of_injective g hg h1, hB ▸ IsLin2Type.map_of_injective' g hg h2⟩

end CFSG.Quasithin.H13.NQCat.A314D
