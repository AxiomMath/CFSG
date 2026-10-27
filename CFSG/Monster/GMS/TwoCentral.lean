module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Monster.GMS

open Subgroup

section Helpers

private theorem mem_map_center_subtype_iff {H : Type*} [Group H] {K : Subgroup H} {g : H} :
    g ∈ (center K).map K.subtype ↔ g ∈ K ∧ ∀ k ∈ K, k * g = g * k := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun k hk => congrArg Subtype.val (mem_center_iff.mp hc ⟨k, hk⟩)⟩
  · rintro ⟨hg, hcomm⟩
    exact ⟨⟨g, hg⟩, mem_center_iff.mpr fun k => Subtype.ext (hcomm k k.2), rfl⟩

private theorem mem_map_map_center_iff {G : Type*} [Group G] {C : Subgroup G} {K : Subgroup C}
    {w : G} :
    w ∈ ((center K).map K.subtype).map C.subtype ↔
      w ∈ K.map C.subtype ∧ ∀ x ∈ K.map C.subtype, x * w = w * x := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := mem_map_center_subtype_iff.mp hk
    refine ⟨⟨k, hk'.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hk'.2 y hy)
  · rintro ⟨⟨k, hkK, rfl⟩, hcomm⟩
    refine ⟨k, mem_map_center_subtype_iff.mpr ⟨hkK, fun y hy => ?_⟩, rfl⟩
    exact Subtype.ext (hcomm y.1 ⟨y, hy, rfl⟩)

private theorem eq_of_mem_zpowers_of_ne_one {H : Type*} [Group H] {z w : H} (hz : orderOf z = 2)
    (hw : w ∈ zpowers z) (hw1 : w ≠ 1) : w = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rw [← zpow_mod_orderOf, hz] at hw1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · simp [h] at hw1
  · simp [h]

private theorem normal_pCore (p : ℕ) (H : Type*) [Group H] : (pCore p H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

end Helpers

section Main

variable {G : Type*} [Group G] {z : G}
  (hz : orderOf z = 2)
  (hQ : IsExtraspecialPGroup 2 (pCore 2 (Subgroup.centralizer ({z} : Set G))))
  (hcon : Subgroup.centralizer (pCore 2 (Subgroup.centralizer ({z} : Set G)) :
      Set (Subgroup.centralizer ({z} : Set G))) ≤ pCore 2 (Subgroup.centralizer ({z} : Set G)))

include hcon in
theorem mem_pCore_centralizer_self :
    (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      pCore 2 (Subgroup.centralizer ({z} : Set G)) := by
  refine hcon (Subgroup.mem_centralizer_iff.mpr fun q _ => ?_)
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp q.2)

include hz hQ hcon

theorem center_pCore_map_eq_zpowers :
    ((Subgroup.center (pCore 2 (Subgroup.centralizer ({z} : Set G)))).map
        (pCore 2 (Subgroup.centralizer ({z} : Set G))).subtype).map
      (Subgroup.centralizer ({z} : Set G)).subtype = Subgroup.zpowers z := by
  have hζ := mem_pCore_centralizer_self hcon
  let ζ : pCore 2 (Subgroup.centralizer ({z} : Set G)) :=
    ⟨⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, hζ⟩
  have hζc : ζ ∈ center (pCore 2 (Subgroup.centralizer ({z} : Set G))) := by
    rw [mem_center_iff]
    intro q
    exact Subtype.ext (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp q.1.2))
  have hord : orderOf ζ = 2 :=
    (orderOf_coe ζ).symm.trans
      ((orderOf_coe (ζ : Subgroup.centralizer ({z} : Set G))).symm.trans hz)
  have hfin : Finite (center (pCore 2 (Subgroup.centralizer ({z} : Set G)))) :=
    Nat.finite_of_card_ne_zero (by rw [hQ.2.2.2]; norm_num)
  have hcenter : zpowers ζ = center (pCore 2 (Subgroup.centralizer ({z} : Set G))) := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hζc) ?_
    rw [hQ.2.2.2, Nat.card_zpowers, hord]
  rw [← hcenter, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem center_sylow_map_eq_zpowers (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    ((Subgroup.center (S : Subgroup (Subgroup.centralizer ({z} : Set G)))).map
        (S : Subgroup (Subgroup.centralizer ({z} : Set G))).subtype).map
      (Subgroup.centralizer ({z} : Set G)).subtype = Subgroup.zpowers z := by
  have : (pCore 2 (Subgroup.centralizer ({z} : Set G))).Normal := normal_pCore _ _
  have hQS : pCore 2 (Subgroup.centralizer ({z} : Set G)) ≤ S := hQ.1.le_sylow_of_normal S
  have hζ := mem_pCore_centralizer_self hcon
  refine le_antisymm ?_ (zpowers_le.mpr ?_)
  · rw [← center_pCore_map_eq_zpowers hz hQ hcon]
    intro w hw
    rw [mem_map_map_center_iff] at hw ⊢
    obtain ⟨⟨c, hcS, rfl⟩, hcomm⟩ := hw
    have hcQ : c ∈ pCore 2 (Subgroup.centralizer ({z} : Set G)) := by
      refine hcon (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
      exact Subtype.ext (hcomm q.1 ⟨q, hQS hq, rfl⟩)
    refine ⟨⟨c, hcQ, rfl⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hcomm q.1 ⟨q, hQS hq, rfl⟩
  · rw [mem_map_map_center_iff]
    refine ⟨⟨_, hQS hζ, rfl⟩, ?_⟩
    rintro _ ⟨s, _, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp s.2

section Finite

variable [Finite G]

theorem exists_sylow_eq_map_of_sylow_centralizer
    (S : Sylow 2 (Subgroup.centralizer ({z} : Set G))) :
    ∃ P : Sylow 2 G, (P : Subgroup G) =
      (S : Subgroup (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := by
  have hS := center_sylow_map_eq_zpowers hz hQ hcon S
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  obtain ⟨P, hSP⟩ :=
    (S.isPGroup'.map (Subgroup.centralizer ({z} : Set G)).subtype).exists_le_sylow
  refine ⟨P, le_antisymm ?_ hSP⟩
  have hPC : ∀ x ∈ (P : Subgroup G), x ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ (S : Subgroup (Subgroup.centralizer ({z} : Set G))).map
        (Subgroup.centralizer ({z} : Set G)).subtype := by
    intro x hxP hxC
    have hR : IsPGroup 2 ((P : Subgroup G).comap (Subgroup.centralizer ({z} : Set G)).subtype) :=
      P.isPGroup'.comap_subtype
    have hSR := S.is_maximal' hR (map_le_iff_le_comap.mp hSP)
    exact ⟨⟨x, hxC⟩, hSR ▸ (show x ∈ (P : Subgroup G) from hxP), rfl⟩
  have hzS : z ∈ (S : Subgroup (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype :=
    (mem_map_map_center_iff.mp (hS ▸ Subgroup.mem_zpowers z)).1
  have hzP : z ∈ (P : Subgroup G) := hSP hzS
  have hcentral : ∀ x ∈ (P : Subgroup G), x * z = z * x := by
    have : Nontrivial (P : Subgroup G) := ⟨⟨⟨z, hzP⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    have : Nontrivial (Subgroup.center (P : Subgroup G)) := P.isPGroup'.center_nontrivial
    obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center (P : Subgroup G))
    have hwP : ∀ x ∈ (P : Subgroup G), x * w.1.1 = w.1.1 * x := fun x hx =>
      congrArg Subtype.val (mem_center_iff.mp w.2 ⟨x, hx⟩)
    have hwz : w.1.1 ∈ Subgroup.zpowers z := by
      rw [← hS, mem_map_map_center_iff]
      refine ⟨hPC _ w.1.2 (Subgroup.mem_centralizer_singleton_iff.mpr (hwP z hzP).symm), ?_⟩
      exact fun x hx => hwP x (hSP hx)
    have hwz' : w.1.1 = z :=
      eq_of_mem_zpowers_of_ne_one hz hwz fun h => hw1 (Subtype.ext (Subtype.ext h))
    exact fun x hx => hwz' ▸ hwP x hx
  exact fun x hx => hPC x hx (Subgroup.mem_centralizer_singleton_iff.mpr (hcentral x hx))

theorem exists_sylow_center_map_eq_zpowers :
    ∃ P : Sylow 2 G, (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype =
      Subgroup.zpowers z := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_map_of_sylow_centralizer hz hQ hcon default
  refine ⟨P, ?_⟩
  rw [← center_sylow_map_eq_zpowers hz hQ hcon default]
  ext w
  rw [mem_map_center_subtype_iff, mem_map_map_center_iff, hP]

theorem isConj_of_mem_center_sylow (P : Sylow 2 G) {t : G} (ht : orderOf t = 2)
    (hmem : t ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) :
    IsConj z t := by
  obtain ⟨P₀, hP₀⟩ := exists_sylow_center_map_eq_zpowers hz hQ hcon
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P₀ P
  obtain ⟨htP, htc⟩ := mem_map_center_subtype_iff.mp hmem
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htP
  obtain ⟨s, hsP, rfl⟩ := htP
  have hsc : ∀ k ∈ (P₀ : Subgroup G), k * s = s * k := by
    intro k hk
    have h := htc (MulAut.conj g • k) (by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj g) _ hk)
    apply (MulAut.conj g).injective
    simpa [map_mul] using h
  have hs : s ∈ Subgroup.zpowers z := hP₀ ▸ mem_map_center_subtype_iff.mpr ⟨hsP, hsc⟩
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at ht
  have hsz : s = z := eq_of_mem_zpowers_of_ne_one hz hs hs1
  exact isConj_iff.mpr ⟨g, by simp [hsz]⟩

end Finite

end Main

end CFSG.Monster.GMS
