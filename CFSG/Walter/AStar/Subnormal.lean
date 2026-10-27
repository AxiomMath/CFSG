module

public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Walter

variable {G : Type*} [Group G]

theorem conj_mem_map_of_characteristic {X : Subgroup G} {D : Subgroup X} [hD : D.Characteristic]
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ D.map X.subtype) :
    g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

variable [Finite G]

theorem map_pPrimeCore_le_of_isSubnormal {X : Subgroup G} (hX : X.IsSubnormal) :
    (pPrimeCore 2 X).map X.subtype ≤ pPrimeCore 2 G := by
  have key : ∀ {X Z : Subgroup G}, X ≤ Z → Z ≤ Subgroup.normalizer (X : Set G) →
      (pPrimeCore 2 X).map X.subtype ≤ (pPrimeCore 2 Z).map Z.subtype := by
    intro X Z hXZ hZN
    have hLZ : (pPrimeCore 2 X).map X.subtype ≤ Z := (Subgroup.map_subtype_le _).trans hXZ
    have hle : ((pPrimeCore 2 X).map X.subtype).subgroupOf Z ≤ pPrimeCore 2 Z := by
      apply le_sSup
      refine ⟨⟨fun l hl z => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic (hZN z.2) hl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLZ).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact pPrimeCore_coprime_card
    calc (pPrimeCore 2 X).map X.subtype
        = (((pPrimeCore 2 X).map X.subtype).subgroupOf Z).map Z.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLZ).symm
      _ ≤ (pPrimeCore 2 Z).map Z.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic ?_ hl⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
      exact pPrimeCore_coprime_card
  | step X Z hXZ hZ hN ih =>
    exact (key hXZ ((Subgroup.normal_subgroupOf_iff_le_normalizer hXZ).mp hN)).trans ih

theorem eq_bot_of_isSubnormal_of_odd (hO : pPrimeCore 2 G = ⊥) {K : Subgroup G}
    (hK : K.IsSubnormal) (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have htop : pPrimeCore 2 K = ⊤ := by
    apply le_antisymm le_top
    exact le_sSup ⟨inferInstance, by
      rw [Subgroup.card_top]
      exact Nat.coprime_two_left.mpr hodd⟩
  have h := map_pPrimeCore_le_of_isSubnormal hK
  rw [htop, hO, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact le_bot_iff.mp h

theorem exists_sylow_map_eq_inf_of_isSubnormal {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {H : Subgroup G} (hH : H.IsSubnormal) :
    ∃ P : Sylow p H, (P : Subgroup H).map H.subtype = (S : Subgroup G) ⊓ H := by
  induction hH with
  | top =>
    let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨S.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, inf_top_eq]
    convert Subgroup.map_id (S : Subgroup G)
    ext x
    rfl
  | step H K hHK hK hN ih =>
    obtain ⟨PK, hPK⟩ := ih
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal PK (N := H.subgroupOf K)
    let e : H.subgroupOf K ≃* H := Subgroup.subgroupOfEquivOfLe hHK
    have he : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨Q.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : H.subtype.comp e.toMonoidHom = K.subtype.comp (H.subgroupOf K).subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, hQ, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem,
      Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hPK, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHK, inf_assoc, inf_eq_right.mpr hHK]

theorem sylow_inf_ne_bot_of_isSubnormal {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    {H : Subgroup G} (hH : H.IsSubnormal) (hp : p ∣ Nat.card H) :
    (S : Subgroup G) ⊓ H ≠ ⊥ := by
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf_of_isSubnormal S hH
  rw [← hP]
  intro h
  rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  exact P.ne_bot_of_dvd_card hp h

end CFSG.Walter
