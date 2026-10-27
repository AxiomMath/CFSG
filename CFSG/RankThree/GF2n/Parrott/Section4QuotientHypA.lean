module

public import CFSG.RankThree.GF2n.Parrott.Section4Theorem4
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.RankThree.GF2n.Parrott.LiftClaimC
public import CFSG.RankThree.GF2n.Parrott.CaseII

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Quotient

instance zpowers_subgroupOf_centralizer_normal (z₁ : G) :
    ((Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G))).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg : (g : G) * z₁ = z₁ * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have h1 : (g : G) * z₁ ^ k = z₁ ^ k * (g : G) := (Commute.zpow_right hg k).eq
    have : ((g * n * g⁻¹ : ↥(Subgroup.centralizer ({z₁} : Set G))) : G) = (n : G) := by
      show (g : G) * (n : G) * (g : G)⁻¹ = n
      rw [← hk, h1]; group
    rw [this]
    exact hn

abbrev QuotC (z₁ : G) : Type :=
  ↥(Subgroup.centralizer ({z₁} : Set G)) ⧸
    (Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G))

variable {z₁ : G}

theorem H_le_centralizer_of_mem_centerIn (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) : H z ≤ Subgroup.centralizer ({z₁} : Set G) := by
  intro x hx
  have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz₁'.2 x hx)

@[expose] def quotW (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) : QuotC z₁ :=
  QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G)))

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {c : G} (hz₁2 : orderOf z₁ = 2)
    (hc : c ∈ Subgroup.zpowers z₁) : c = 1 ∨ c = z₁ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : z₁ ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hz₁2]
    exact pow_orderOf_eq_one z₁
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem centralizer_quotW_eq_map (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Subgroup.centralizer ({quotW hzC} : Set (QuotC z₁)) =
      ((H z).subgroupOf (Subgroup.centralizer ({z₁} : Set G))).map
        (QuotientGroup.mk' ((Subgroup.zpowers z₁).subgroupOf
          (Subgroup.centralizer ({z₁} : Set G)))) := by
  have hHC := H_le_centralizer_of_mem_centerIn hZ hz₁
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have h1 : (QuotientGroup.mk (x * ⟨z, hzC⟩) :
        ↥(Subgroup.centralizer ({z₁} : Set G)) ⧸ (Subgroup.zpowers z₁).subgroupOf
          (Subgroup.centralizer ({z₁} : Set G))) =
        QuotientGroup.mk (⟨z, hzC⟩ * x) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    have h2 : z⁻¹ * (x : G)⁻¹ * z * (x : G) ∈ Subgroup.zpowers z₁ := by
      have : (((x * ⟨z, hzC⟩)⁻¹ * (⟨z, hzC⟩ * x) :
          ↥(Subgroup.centralizer ({z₁} : Set G))) : G) = z⁻¹ * (x : G)⁻¹ * z * (x : G) := by
        show ((x : G) * z)⁻¹ * (z * (x : G)) = _
        group
      rwa [this] at h1
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    show (x : G) ∈ H z
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz₁2 h2 with h3 | h3
    ·
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have e : (x : G) * z * (z⁻¹ * (x : G)⁻¹ * z * (x : G)) = z * (x : G) := by group
      rw [h3, mul_one] at e
      exact e
    · exfalso
      have hconj : IsConj z (z * z₁) := by
        refine isConj_iff.mpr ⟨(x : G)⁻¹, ?_⟩
        have e : z * (z⁻¹ * (x : G)⁻¹ * z * (x : G)) = (x : G)⁻¹ * z * ((x : G)⁻¹)⁻¹ := by group
        rw [← e, h3]
      have hzz₁ := (exists_z1_mul h hz₁ hz₁z hz₁2).1
      have h4 := eq_of_isConj_of_mem_centerIn_J h hZ (z_mem_centerIn_J h) hzz₁ hconj
      have h5 : z₁ = 1 := by
        calc z₁ = z⁻¹ * (z * z₁) := by group
          _ = z⁻¹ * z := by rw [← h4]
          _ = 1 := by group
      rw [h5, orderOf_one] at hz₁2
      exact absurd hz₁2 (by norm_num)
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxz : (x : G) * z = z * (x : G) := by
      have := Subgroup.mem_subgroupOf.mp hx
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    show QuotientGroup.mk' _ x *
        QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
      QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) *
        QuotientGroup.mk' _ x
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hxz

@[expose] noncomputable def quotMk (z₁ : G) : ↥(Subgroup.centralizer ({z₁} : Set G)) →* QuotC z₁ :=
  QuotientGroup.mk' ((Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)))

@[expose] noncomputable def quotH (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) : ↥(H z) →* QuotC z₁ :=
  (quotMk z₁).comp (Subgroup.inclusion (H_le_centralizer_of_mem_centerIn hZ hz₁))

theorem mem_ker_quotH_iff (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (x : ↥(H z)) : x ∈ (quotH hZ hz₁).ker ↔ (x : G) ∈ Subgroup.zpowers z₁ := by
  rw [MonoidHom.mem_ker, quotH, MonoidHom.comp_apply, quotMk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem ker_quotH_eq (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z)) :
    (quotH hZ hz₁).ker = (Subgroup.zpowers z₁).subgroupOf (H z) :=
  Subgroup.ext (mem_ker_quotH_iff hZ hz₁)

theorem zpowers_le_J_of_mem_centerIn (hz₁ : z₁ ∈ centerIn (J z)) : Subgroup.zpowers z₁ ≤ J z :=
  Subgroup.zpowers_le.mpr hz₁.1

theorem card_ker_quotH (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁2 : orderOf z₁ = 2) : Nat.card (quotH hZ hz₁).ker = 2 := by
  rw [ker_quotH_eq hZ hz₁]
  have hle : Subgroup.zpowers z₁ ≤ H z := (zpowers_le_J_of_mem_centerIn hz₁).trans J_le_H
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hz₁2]

theorem ker_quotH_le_J (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z)) :
    (quotH hZ hz₁).ker ≤ (J z).subgroupOf (H z) := by
  rw [ker_quotH_eq hZ hz₁]
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr
    (zpowers_le_J_of_mem_centerIn hz₁ (Subgroup.mem_subgroupOf.mp hx))

theorem quotH_mem_H (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) (x : ↥(H z)) :
    quotH hZ hz₁ x ∈ H (quotW hzC) := by
  rw [H_eq_centralizer, centralizer_quotW_eq_map h hZ hz₁ hz₁z hz₁2 hzC]
  exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion (H_le_centralizer_of_mem_centerIn hZ hz₁) x,
    Subgroup.mem_subgroupOf.mpr x.2, rfl⟩

@[expose] noncomputable def quotHH (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) : ↥(H z) →* ↥(H (quotW hzC)) :=
  (quotH hZ hz₁).codRestrict (H (quotW hzC)) (quotH_mem_H h hZ hz₁ hz₁z hz₁2 hzC)

theorem quotHH_surjective (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Function.Surjective (quotHH h hZ hz₁ hz₁z hz₁2 hzC) := by
  intro y
  have hy : (y : QuotC z₁) ∈ Subgroup.centralizer ({quotW hzC} : Set (QuotC z₁)) := y.2
  rw [centralizer_quotW_eq_map h hZ hz₁ hz₁z hz₁2 hzC] at hy
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
  apply Subtype.ext
  rw [← hxy]
  rfl

theorem ker_quotHH (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    (quotHH h hZ hz₁ hz₁z hz₁2 hzC).ker = (quotH hZ hz₁).ker :=
  MonoidHom.ker_codRestrict _ _ _

theorem isPGroup_ker_quotHH (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    IsPGroup 2 (quotHH h hZ hz₁ hz₁z hz₁2 hzC).ker := by
  rw [ker_quotHH, ker_quotH_eq hZ hz₁]
  have h2 : IsPGroup 2 (Subgroup.zpowers z₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₁2]; norm_num)
  exact h2.comap_subtype

theorem J_quotW_eq (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    J (quotW hzC) = ((J z).subgroupOf (H z)).map (quotH hZ hz₁) := by
  have h1 := map_pCore_eq_of_surjective_of_isPGroup_ker (p := 2)
    (quotHH h hZ hz₁ hz₁z hz₁2 hzC) (quotHH_surjective h hZ hz₁ hz₁z hz₁2 hzC)
    (isPGroup_ker_quotHH h hZ hz₁ hz₁z hz₁2 hzC)
  show (pCore 2 ↥(H (quotW hzC))).map (H (quotW hzC)).subtype = _
  rw [← h1, Subgroup.map_map, J_subgroupOf_eq_pCore z]
  rfl

theorem card_J_quotW (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) : Nat.card (J (quotW hzC)) = 2 ^ 9 := by
  rw [J_quotW_eq h hZ hz₁ hz₁z hz₁2 hzC, ← Subgroup.relIndex_ker (K := (J z).subgroupOf (H z))]
  have h1 := Subgroup.relIndex_mul_card (quotH hZ hz₁).ker ((J z).subgroupOf (H z))
  rw [inf_eq_left.mpr (ker_quotH_le_J hZ hz₁), card_ker_quotH hZ hz₁ hz₁2] at h1
  have h2 : Nat.card ((J z).subgroupOf (H z)) = 2 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv, card_J h]
  rw [h2] at h1
  omega

theorem zpowers_inf_zpowers_eq_bot_of_orderOf_eq_two (hz : orderOf z = 2)
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2) :
    Subgroup.zpowers z ⊓ Subgroup.zpowers z₁ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz₁2 hx.2 with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hx.1) hz₁z

theorem quotW_mul_self (h : Tim79a.ParrottHyp z) (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    quotW hzC * quotW hzC = 1 := by
  have h2 : z * z = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at h1
  show QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) *
      QuotientGroup.mk (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = 1
  rw [← QuotientGroup.mk_mul]
  have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z, hzC⟩ = 1 := Subtype.ext h2
  rw [this]
  exact QuotientGroup.mk_one _

theorem quotW_ne_one (h : Tim79a.ParrottHyp z) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hz₁2 : orderOf z₁ = 2) (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    quotW hzC ≠ 1 := by
  intro h1
  have h2 : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) ∈
      (Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) :=
    (QuotientGroup.eq_one_iff _).mp h1
  have h3 : z ∈ Subgroup.zpowers z₁ := Subgroup.mem_subgroupOf.mp h2
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz₁2 h3 with h4 | h4
  · have := h.1
    rw [h4, orderOf_one] at this
    exact absurd this (by norm_num)
  · exact hz₁z (h4 ▸ Subgroup.mem_zpowers z)

theorem orderOf_quotW (h : Tim79a.ParrottHyp z) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hz₁2 : orderOf z₁ = 2) (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    orderOf (quotW hzC) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact quotW_mul_self h hzC) (quotW_ne_one h hz₁z hz₁2 hzC)

theorem quotH_z (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) (hzH : z ∈ H z) :
    quotH hZ hz₁ ⟨z, hzH⟩ = quotW hzC := rfl

theorem commutator_J_quotW (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    ⁅J (quotW hzC), J (quotW hzC)⁆ = Subgroup.zpowers (quotW hzC) := by
  rw [J_quotW_eq h hZ hz₁ hz₁z hz₁2 hzC, ← Subgroup.map_commutator]
  have hzH : z ∈ H z := z_mem_H
  have h1 : ⁅(J z).subgroupOf (H z), (J z).subgroupOf (H z)⁆ =
      Subgroup.zpowers (⟨z, hzH⟩ : ↥(H z)) := by
    apply Subgroup.map_injective (H z).subtype_injective
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le (J_le_H (z := z))]
    have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
    rw [hcomm]
    rfl
  rw [h1, MonoidHom.map_zpowers]
  rfl

theorem mem_J_quotW_iff (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) (y : QuotC z₁) :
    y ∈ J (quotW hzC) ↔ ∃ x : ↥(H z), (x : G) ∈ J z ∧ quotH hZ hz₁ x = y := by
  rw [J_quotW_eq h hZ hz₁ hz₁z hz₁2 hzC, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem comm_mem_zpowers_of_quotH_commute (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) {x : ↥(H z)} {j : G} (hjH : j ∈ H z)
    (h1 : quotH hZ hz₁ ⟨j, hjH⟩ * quotH hZ hz₁ x = quotH hZ hz₁ x * quotH hZ hz₁ ⟨j, hjH⟩) :
    (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈ Subgroup.zpowers z₁ := by
  rw [← map_mul, ← map_mul] at h1
  have h2 : ((⟨j, hjH⟩ * x)⁻¹ * (x * ⟨j, hjH⟩) : ↥(H z)) ∈ (quotH hZ hz₁).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1]
    simp
  have := (mem_ker_quotH_iff hZ hz₁ _).mp h2
  have e : (((⟨j, hjH⟩ * x)⁻¹ * (x * ⟨j, hjH⟩) : ↥(H z)) : G) =
      (x : G)⁻¹ * j⁻¹ * (x : G) * j := by
    show ((j : G) * (x : G))⁻¹ * ((x : G) * j) = _
    group
  rwa [e] at this

theorem mul_mul_inv_eq_mul_of_mem_zpowers (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) {x j : G} (hxH : x ∈ H z)
    (hc : x⁻¹ * j⁻¹ * x * j ∈ Subgroup.zpowers z₁) :
    x * j * x⁻¹ = j * (x⁻¹ * j⁻¹ * x * j) := by
  have hz₁' : z₁ ∈ centerIn (H z) := hZ ▸ hz₁
  have hcc : (x⁻¹ * j⁻¹ * x * j) ∈ centerIn (H z) := by
    have : Subgroup.zpowers z₁ ≤ centerIn (H z) := Subgroup.zpowers_le.mpr hz₁'
    exact this hc
  have hxc : x * (x⁻¹ * j⁻¹ * x * j) = (x⁻¹ * j⁻¹ * x * j) * x :=
    Subgroup.mem_centralizer_iff.mp hcc.2 x hxH
  have e1 : x * (x⁻¹ * j⁻¹ * x * j) * x⁻¹ = j⁻¹ * x * j * x⁻¹ := by group
  have e2 : x * (x⁻¹ * j⁻¹ * x * j) * x⁻¹ = (x⁻¹ * j⁻¹ * x * j) := by
    rw [hxc]; group
  have e3 : j⁻¹ * x * j * x⁻¹ = x⁻¹ * j⁻¹ * x * j := by rw [← e1, e2]
  calc x * j * x⁻¹ = j * (j⁻¹ * x * j * x⁻¹) := by group
    _ = j * (x⁻¹ * j⁻¹ * x * j) := by rw [e3]

theorem centerIn_J_quotW (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    centerIn (J (quotW hzC)) = Subgroup.zpowers (quotW hzC) := by
  have hzH : z ∈ H z := z_mem_H
  have hz₁H : z₁ ∈ H z := J_le_H hz₁.1
  apply le_antisymm
  · rintro y ⟨hyJ, hyC⟩
    obtain ⟨x, hxJ, rfl⟩ := (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC y).mp hyJ
    have hxZ : (x : G) ∈ centerIn (J z) := by
      refine ⟨hxJ, ?_⟩
      show (x : G) ∈ Subgroup.centralizer ((J z : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjH : j ∈ H z := J_le_H hj
      have hjw : quotH hZ hz₁ ⟨j, hjH⟩ ∈ J (quotW hzC) :=
        (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC _).mpr ⟨⟨j, hjH⟩, hj, rfl⟩
      have h3 := comm_mem_zpowers_of_quotH_commute hZ hz₁ hjH
        (Subgroup.mem_centralizer_iff.mp hyC _ hjw)
      have h4 : (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈ Subgroup.zpowers z := by
        have h5 : (x : G)⁻¹ * j⁻¹ * (x : G) * j = ⁅(x : G)⁻¹, j⁻¹⁆ := by
          rw [commutatorElement_def]; group
        rw [h5]
        have h6 : ⁅(x : G)⁻¹, j⁻¹⁆ ∈ ⁅J z, J z⁆ :=
          Subgroup.commutator_mem_commutator ((J z).inv_mem hxJ) ((J z).inv_mem hj)
        have hcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
        rwa [hcomm] at h6
      have h7 := zpowers_inf_zpowers_eq_bot_of_orderOf_eq_two h.1 hz₁z hz₁2
      have h8 : (x : G)⁻¹ * j⁻¹ * (x : G) * j = 1 := by
        have : (x : G)⁻¹ * j⁻¹ * (x : G) * j ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers z₁ :=
          Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [h7, Subgroup.mem_bot] at this
        exact this
      have e : (j : G) * (x : G) * ((x : G)⁻¹ * j⁻¹ * (x : G) * j) = (x : G) * j := by group
      rw [h8, mul_one] at e
      exact e
    rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp hxZ with h1 | h1 | h1 | h1
    · have : x = 1 := Subtype.ext h1
      rw [this, map_one]
      exact Subgroup.one_mem _
    · have : x = ⟨z, hzH⟩ := Subtype.ext h1
      rw [this, quotH_z hZ hz₁ hzC hzH]
      exact Subgroup.mem_zpowers _
    · have hxk : x ∈ (quotH hZ hz₁).ker :=
        (mem_ker_quotH_iff hZ hz₁ x).mpr (h1 ▸ Subgroup.mem_zpowers z₁)
      rw [MonoidHom.mem_ker.mp hxk]
      exact Subgroup.one_mem _
    · have : x = ⟨z, hzH⟩ * ⟨z₁, hz₁H⟩ := Subtype.ext h1
      have hk : (⟨z₁, hz₁H⟩ : ↥(H z)) ∈ (quotH hZ hz₁).ker :=
        (mem_ker_quotH_iff hZ hz₁ _).mpr (Subgroup.mem_zpowers z₁)
      rw [this, map_mul, MonoidHom.mem_ker.mp hk, mul_one, quotH_z hZ hz₁ hzC hzH]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine ⟨?_, ?_⟩
    · exact (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC _).mpr ⟨⟨z, hzH⟩, z_mem_J h, rfl⟩
    · show quotW hzC ∈ Subgroup.centralizer ((J (quotW hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x, hxJ, rfl⟩ := (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC y).mp hy
      rw [← quotH_z hZ hz₁ hzC hzH, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) (x : G) hxJ

theorem isExtraspecial2_J_quotW (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    IsExtraspecial2 (J (quotW hzC)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (pCore_isPGroup (p := 2) (G := ↥(H (quotW hzC)))).map (H (quotW hzC)).subtype
  · rw [← CFSG.centerIn_eq_map_center, commutator_J_quotW h hZ hz₁ hz₁z hz₁2 hzC,
      centerIn_J_quotW h hZ hz₁ hz₁z hz₁2 hzC]
  · rw [commutator_J_quotW h hZ hz₁ hz₁z hz₁2 hzC, Nat.card_zpowers,
      orderOf_quotW h hz₁z hz₁2 hzC]

theorem centralizer_J_quotW_le (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    H (quotW hzC) ⊓
      Subgroup.centralizer ((J (quotW hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁)) ≤
      J (quotW hzC) := by
  rintro y ⟨hyH, hyC⟩
  obtain ⟨x, hx⟩ := quotHH_surjective h hZ hz₁ hz₁z hz₁2 hzC ⟨y, hyH⟩
  have hxy : quotH hZ hz₁ x = y := congrArg Subtype.val hx
  have hxJ : (x : G) ∈ J z := by
    apply mem_J_of_conjZ_eq_one_of_conjV_eq_one h
    · apply MulEquiv.ext
      intro c
      apply Subtype.ext
      rw [conjZ_apply_coe]
      have hcH : (c : G) ∈ centerIn (H z) := hZ ▸ c.2
      have h1 := Subgroup.mem_centralizer_iff.mp hcH.2 (x : G) x.2
      show (x : G) * c * (x : G)⁻¹ = c
      rw [h1]
      group
    · apply MulEquiv.ext
      intro v
      obtain ⟨j, rfl⟩ := QuotientV.pi_surjective z v
      rw [conjV_pi_conj h x j.2, MulAut.one_apply]
      have hjH : (j : G) ∈ H z := J_le_H j.2
      have hjw : quotH hZ hz₁ ⟨j, hjH⟩ ∈ J (quotW hzC) :=
        (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC _).mpr ⟨⟨j, hjH⟩, j.2, rfl⟩
      have hc := comm_mem_zpowers_of_quotH_commute hZ hz₁ hjH
        (by rw [hxy]; exact Subgroup.mem_centralizer_iff.mp hyC _ hjw)
      have he := mul_mul_inv_eq_mul_of_mem_zpowers hZ hz₁ x.2 hc
      have hcZ : (x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G) ∈ centerIn (J z) :=
        (Subgroup.zpowers_le.mpr hz₁) hc
      have hcJ : (x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G) ∈ J z := hcZ.1
      have e : (⟨(x : G) * j * (x : G)⁻¹, H_conj_mem_J x j.2⟩ : J z) =
          ⟨(j : G) * ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)), (J z).mul_mem j.2 hcJ⟩ :=
        Subtype.ext he
      rw [e]
      have h2 := pi_mk_mul_J (z := z) (j : G) ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)) j.2 hcJ
      rw [show (⟨(j : G) * ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)),
        (J z).mul_mem j.2 hcJ⟩ : J z) = ⟨(j : G) * ((x : G)⁻¹ * (j : G)⁻¹ * (x : G) * (j : G)),
        (J z).mul_mem j.2 hcJ⟩ from rfl, h2,
        (pi_eq_one_iff_mem_centerIn hcJ).mpr hcZ, mul_one]
  exact (mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC y).mpr ⟨x, hxJ, hxy⟩

theorem nonempty_quotientData_quotW (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Nonempty (QuotientData (quotW hzC) (J_subgroupOf_normal (quotW hzC))) := by
  obtain ⟨_, ⟨D⟩⟩ := parrottQuotientDataExists h
  let D' : QuotientData z (J_subgroupOf_normal z) := D
  let Φ : ↥(H z) →* (↥(H (quotW hzC)) ⧸ (J (quotW hzC)).subgroupOf (H (quotW hzC))) :=
    (QuotientGroup.mk' ((J (quotW hzC)).subgroupOf (H (quotW hzC)))).comp
      (quotHH h hZ hz₁ hz₁z hz₁2 hzC)
  have hΦs : Function.Surjective Φ := by
    intro a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x, hx⟩ := quotHH_surjective h hZ hz₁ hz₁z hz₁2 hzC b
    exact ⟨x, by simp [Φ, hx]⟩
  have hker : Φ.ker = (J z).subgroupOf (H z) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show quotH hZ hz₁ x ∈ J (quotW hzC) ↔ (x : G) ∈ J z
    rw [mem_J_quotW_iff h hZ hz₁ hz₁z hz₁2 hzC]
    constructor
    · rintro ⟨x', hx'J, hx'⟩
      have h1 : x'⁻¹ * x ∈ (quotH hZ hz₁).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hx', inv_mul_cancel]
      have h2 : ((x'⁻¹ * x : ↥(H z)) : G) ∈ J z :=
        zpowers_le_J_of_mem_centerIn hz₁ ((mem_ker_quotH_iff hZ hz₁ _).mp h1)
      have h3 : (x : G) = (x' : G) * ((x'⁻¹ * x : ↥(H z)) : G) := by
        show (x : G) = (x' : G) * ((x' : G)⁻¹ * (x : G))
        group
      rw [h3]
      exact (J z).mul_mem hx'J h2
    · intro hxJ
      exact ⟨x, hxJ, rfl⟩
  exact ⟨{ X := D'.X
           instX := D'.instX
           lie := D'.lie
           iso := (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs).symm.trans
             ((QuotientGroup.quotientMulEquivOfEq hker).trans D'.iso) }⟩

theorem parrottHypA_quotient (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hzC : z ∈ Subgroup.centralizer ({z₁} : Set G)) :
    Tim79a.ParrottHypA (quotW hzC) :=
  ⟨isExtraspecial2_J_quotW h hZ hz₁ hz₁z hz₁2 hzC, card_J_quotW h hZ hz₁ hz₁z hz₁2 hzC,
    commutator_J_quotW h hZ hz₁ hz₁z hz₁2 hzC, centralizer_J_quotW_le h hZ hz₁ hz₁z hz₁2 hzC,
    nonempty_quotientData_quotW h hZ hz₁ hz₁z hz₁2 hzC⟩

end Quotient

end CFSG.RankThree.GF2n.Parrott
