module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KEb

theorem coe_mem_normalizer_map_subtype_iff {G : Type*} [Group G] {W : Subgroup G}
    {X : Subgroup W} {h : W} :
    (h : G) ∈ Subgroup.normalizer ((X.map W.subtype : Subgroup G) : Set G) ↔
      h ∈ Subgroup.normalizer (X : Set W) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hN y
    have h1 := hN (y : G)
    constructor
    · intro hy
      obtain ⟨w, hw, hwe⟩ : (h : G) * (y : G) * (h : G)⁻¹ ∈ X.map W.subtype :=
        h1.mp ⟨y, hy, rfl⟩
      have hwy : w = h * y * h⁻¹ := Subtype.ext (by simpa using hwe)
      rwa [hwy] at hw
    · intro hy
      obtain ⟨w, hw, hwe⟩ := h1.mpr ⟨h * y * h⁻¹, hy, by simp⟩
      have hwy : w = y := Subtype.ext hwe
      rwa [hwy] at hw
  · intro hN g
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨h * w * h⁻¹, (hN w).mp hw, by simp⟩
    · rintro ⟨w, hw, hwe⟩
      have hgW : g ∈ W := by
        have hwe' : (w : G) = (h : G) * g * (h : G)⁻¹ := hwe
        have hg : g = (h : G)⁻¹ * (w : G) * (h : G) := by
          rw [hwe']
          group
        rw [hg]
        exact W.mul_mem (W.mul_mem (W.inv_mem h.2) w.2) h.2
      refine ⟨⟨g, hgW⟩, (hN ⟨g, hgW⟩).mpr ?_, rfl⟩
      have hhg : h * ⟨g, hgW⟩ * h⁻¹ = w := Subtype.ext (by simpa using hwe.symm)
      rwa [hhg]

theorem congr_normalizerMonoidHom_equivMap {G : Type*} [Group G] {W : Subgroup G}
    (X₀ : Subgroup W) {h : W} (hN : h ∈ Subgroup.normalizer (X₀ : Set W))
    (hN' : (h : G) ∈ Subgroup.normalizer ((X₀.map W.subtype : Subgroup G) : Set G)) :
    (MulAut.congr (X₀.equivMapOfInjective W.subtype W.subtype_injective)).toMonoidHom
        (X₀.normalizerMonoidHom ⟨h, hN⟩) =
      (X₀.map W.subtype).normalizerMonoidHom ⟨(h : G), hN'⟩ := by
  ext y
  obtain ⟨x, rfl⟩ := (X₀.equivMapOfInjective W.subtype W.subtype_injective).surjective y
  simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rfl

theorem nonempty_autIn_map_subtype {G : Type*} [Group G] (W : Subgroup G)
    (H₀ X₀ : Subgroup W) :
    Nonempty (Sec4.autIn (H₀.map W.subtype) (X₀.map W.subtype) ≃* Sec4.autIn H₀ X₀) := by
  have hmap : (Sec4.autIn H₀ X₀).map
      (MulAut.congr (X₀.equivMapOfInjective W.subtype W.subtype_injective)).toMonoidHom =
        Sec4.autIn (H₀.map W.subtype) (X₀.map W.subtype) := by
    ext σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
      have hN' : (h : G) ∈ Subgroup.normalizer ((X₀.map W.subtype : Subgroup G) : Set G) :=
        coe_mem_normalizer_map_subtype_iff.mpr hN
      exact Sec4.mem_autIn_iff.mpr ⟨(h : G), hN', Subgroup.mem_map_of_mem W.subtype hH,
        (congr_normalizerMonoidHom_equivMap X₀ hN hN').symm⟩
    · intro hσ
      obtain ⟨g, hN, hgH, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      obtain ⟨h, hH, rfl⟩ := Subgroup.mem_map.mp hgH
      have hNX : h ∈ Subgroup.normalizer (X₀ : Set W) :=
        (coe_mem_normalizer_map_subtype_iff (W := W) (X := X₀) (h := h)).mp hN
      exact Subgroup.mem_map.mpr ⟨X₀.normalizerMonoidHom ⟨h, hNX⟩,
        Sec4.mem_autIn_iff.mpr ⟨h, hNX, hH, rfl⟩, congr_normalizerMonoidHom_equivMap X₀ hNX hN⟩
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
    ((Sec4.autIn H₀ X₀).equivMapOfInjective
      (MulAut.congr (X₀.equivMapOfInjective W.subtype W.subtype_injective)).toMonoidHom
      (MulAut.congr (X₀.equivMapOfInjective W.subtype W.subtype_injective)).injective).symm⟩

theorem typ129IIIcE_map_subtype {G : Type} [Group G] [Finite G] (W : Subgroup G)
    {A Y E : Subgroup W} {x c : W} (h : Typ129IIIcE A c Y x E) :
    Typ129IIIcE (A.map W.subtype) (c : G) (Y.map W.subtype) (x : G) (E.map W.subtype) := by
  obtain ⟨hE27, hEdec, hcEY, hN, ⟨Z, U, hZU, hZUinf, hZcard, hcomm, hU⟩, hΓ⟩ := h
  have hinj : Function.Injective W.subtype := W.subtype_injective
  unfold Typ129IIIcE
  refine ⟨⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 W.subtype E hE27.1,
    ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hE27.2]
  · have hb := congrArg (Subgroup.map W.subtype) hEdec
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_inf_eq _ _ _ hinj] at hb
    exact hb
  · exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_map_of_mem W.subtype (Subgroup.mem_inf.mp hcEY).1,
        Subgroup.mem_map_of_mem W.subtype (Subgroup.mem_inf.mp hcEY).2⟩
  · intro hle
    refine hN ?_
    intro n hn
    have hzc : Subgroup.zpowers (c : G) = (Subgroup.zpowers c).map W.subtype :=
      (MonoidHom.map_zpowers W.subtype c).symm
    have hG : (n : G) ∈ Y.map W.subtype ⊓
        Subgroup.normalizer ((E.map W.subtype : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem W.subtype (Subgroup.mem_inf.mp hn).1,
        coe_mem_normalizer_map_subtype_iff.mpr (Subgroup.mem_inf.mp hn).2⟩
    have hG' := hle hG
    rw [hzc] at hG'
    exact coe_mem_normalizer_map_subtype_iff.mp hG'
  · refine ⟨Z.map W.subtype, U.map W.subtype, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_sup, ← Subgroup.map_sup, hZU]
    · rw [← Subgroup.map_inf_eq _ _ _ hinj, hZUinf, Subgroup.map_bot]
    · rw [Subgroup.card_map_of_injective hinj, hZcard]
    · intro z hz u hu
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hu
      exact congrArg Subtype.val (hcomm z' hz' u' hu')
    · exact Sec13.isHeisThree_of_mulEquiv (U.equivMapOfInjective W.subtype hinj) hU
  · have hYA : (Y ⊔ A).map W.subtype = Y.map W.subtype ⊔ A.map W.subtype :=
      Subgroup.map_sup Y A W.subtype
    have hφ := nonempty_autIn_map_subtype W (Y ⊔ A) E
    rw [hYA] at hφ
    obtain ⟨φ⟩ := hφ
    obtain ⟨ψ⟩ := hΓ
    exact ⟨φ.trans ψ⟩

end Hering129KEb

end CFSG.RankThree.PartTwo.Sec12
