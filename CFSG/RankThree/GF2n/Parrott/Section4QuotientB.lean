module

public import CFSG.RankThree.GF2n.Parrott.Section4QuotientHypA
import CFSG.GroupTheory.IndexTwoSimpleQuotient
public import CFSG.RankThree.GF2n.Parrott.Section4G0TheoremA

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z z₁ : G}

omit [Finite G] in
theorem z₁_mem_centralizer (z₁ : G) : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

omit [Finite G] in
theorem zpowers_le_centralizer (z₁ : G) :
    Subgroup.zpowers z₁ ≤ Subgroup.centralizer ({z₁} : Set G) :=
  Subgroup.zpowers_le.mpr (z₁_mem_centralizer z₁)

omit [Finite G] in
theorem quotMk_surjective (z₁ : G) : Function.Surjective (quotMk z₁) :=
  QuotientGroup.mk'_surjective _

omit [Finite G] in
theorem mem_ker_quotMk_iff (x : ↥(Subgroup.centralizer ({z₁} : Set G))) :
    quotMk z₁ x = 1 ↔ (x : G) ∈ Subgroup.zpowers z₁ := by
  show QuotientGroup.mk' _ x = 1 ↔ _
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem card_ker_quotMk (hz₁2 : orderOf z₁ = 2) : Nat.card (quotMk z₁).ker = 2 := by
  have h1 : (quotMk z₁).ker =
      (Subgroup.zpowers z₁).subgroupOf (Subgroup.centralizer ({z₁} : Set G)) :=
    QuotientGroup.ker_mk' _
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le_centralizer z₁)).toEquiv,
    Nat.card_zpowers, hz₁2]

@[expose] noncomputable def preC (z₁ : G) (S : Subgroup (QuotC z₁)) : Subgroup G :=
  (S.comap (quotMk z₁)).map (Subgroup.centralizer ({z₁} : Set G)).subtype

omit [Finite G] in
theorem mem_preC {S : Subgroup (QuotC z₁)} {x : G} :
    x ∈ preC z₁ S ↔ ∃ hx : x ∈ Subgroup.centralizer ({z₁} : Set G), quotMk z₁ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hS⟩
    exact ⟨⟨x, hx⟩, hS, rfl⟩

omit [Finite G] in
theorem preC_le_centralizer (S : Subgroup (QuotC z₁)) :
    preC z₁ S ≤ Subgroup.centralizer ({z₁} : Set G) := fun _ hx => (mem_preC.mp hx).1

omit [Finite G] in
theorem preC_mono {S T : Subgroup (QuotC z₁)} (h : S ≤ T) : preC z₁ S ≤ preC z₁ T := by
  intro x hx
  obtain ⟨hxC, hxS⟩ := mem_preC.mp hx
  exact mem_preC.mpr ⟨hxC, h hxS⟩

omit [Finite G] in
theorem zpowers_le_preC (S : Subgroup (QuotC z₁)) : Subgroup.zpowers z₁ ≤ preC z₁ S := by
  rw [Subgroup.zpowers_le]
  refine mem_preC.mpr ⟨z₁_mem_centralizer z₁, ?_⟩
  rw [(mem_ker_quotMk_iff (z₁ := z₁) ⟨z₁, z₁_mem_centralizer z₁⟩).mpr (Subgroup.mem_zpowers z₁)]
  exact S.one_mem

omit [Finite G] in
theorem z₁_mem_preC (S : Subgroup (QuotC z₁)) : z₁ ∈ preC z₁ S :=
  zpowers_le_preC S (Subgroup.mem_zpowers z₁)

omit [Finite G] in
theorem preC_inf (S T : Subgroup (QuotC z₁)) : preC z₁ (S ⊓ T) = preC z₁ S ⊓ preC z₁ T := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxS⟩ := mem_preC.mp hx
    exact ⟨mem_preC.mpr ⟨hxC, hxS.1⟩, mem_preC.mpr ⟨hxC, hxS.2⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hxC, hxS⟩ := mem_preC.mp h1
    obtain ⟨_, hxT⟩ := mem_preC.mp h2
    exact mem_preC.mpr ⟨hxC, hxS, hxT⟩

omit [Finite G] in
theorem quotMk_mem_of_mem_preC {S : Subgroup (QuotC z₁)} {x : G} (hx : x ∈ preC z₁ S) :
    quotMk z₁ ⟨x, preC_le_centralizer S hx⟩ ∈ S := (mem_preC.mp hx).2

omit [Finite G] in
theorem exists_mem_preC_of_mem {S : Subgroup (QuotC z₁)} {a : QuotC z₁} (ha : a ∈ S) :
    ∃ (x : G) (hx : x ∈ preC z₁ S), quotMk z₁ ⟨x, preC_le_centralizer S hx⟩ = a := by
  obtain ⟨y, rfl⟩ := quotMk_surjective z₁ a
  exact ⟨y, mem_preC.mpr ⟨y.2, ha⟩, rfl⟩

theorem card_preC (hz₁2 : orderOf z₁ = 2) (S : Subgroup (QuotC z₁)) :
    Nat.card (preC z₁ S) = 2 * Nat.card S := by
  have hsurj := quotMk_surjective z₁
  have h1 := Subgroup.card_mul_index (S.comap (quotMk z₁))
  have h2 := Subgroup.card_mul_index S
  have h3 : (S.comap (quotMk z₁)).index = S.index := Subgroup.index_comap_of_surjective S hsurj
  have h4 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [card_ker_quotMk hz₁2] at h4
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h5 : Nat.card (S.comap (quotMk z₁)) = 2 * Nat.card S := by
    rw [h3] at h1
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (S.comap (quotMk z₁)) * S.index =
          Nat.card ↥(Subgroup.centralizer ({z₁} : Set G)) := h1
      _ = 2 * Nat.card (QuotC z₁) := h4.symm
      _ = 2 * (Nat.card S * S.index) := by rw [h2]
      _ = 2 * Nat.card S * S.index := by rw [mul_assoc]
  rw [preC, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h5]

omit [Finite G] in
theorem relIndex_preC (S T : Subgroup (QuotC z₁)) :
    (preC z₁ S).relIndex (preC z₁ T) = S.relIndex T := by
  rw [preC, preC, Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _),
    Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (quotMk_surjective z₁)]

structure QuotSetup (z z₁ : G) : Prop where
  h : Tim79a.ParrottHyp z
  hZ : centerIn (J z) = centerIn (H z)
  hz₁ : z₁ ∈ centerIn (J z)
  hz₁z : z₁ ∉ Subgroup.zpowers z
  hz₁2 : orderOf z₁ = 2

theorem QuotSetup.hzC (hs : QuotSetup z z₁) : z ∈ Subgroup.centralizer ({z₁} : Set G) :=
  H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ z_mem_H

theorem QuotSetup.hA (hs : QuotSetup z z₁) : Tim79a.ParrottHypA (quotW hs.hzC) :=
  parrottHypA_quotient hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC

omit [Finite G] in
theorem exists_zpowers_of_quotMk_eq {x y : G} (hx : x ∈ Subgroup.centralizer ({z₁} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z₁} : Set G))
    (h : quotMk z₁ ⟨x, hx⟩ = quotMk z₁ ⟨y, hy⟩) : y⁻¹ * x ∈ Subgroup.zpowers z₁ := by
  have h1 : quotMk z₁ ((⟨y, hy⟩ : ↥(Subgroup.centralizer ({z₁} : Set G)))⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  exact (mem_ker_quotMk_iff _).mp h1

theorem preC_H_quotW (hs : QuotSetup z z₁) : preC z₁ (H (quotW hs.hzC)) = H z := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxw⟩ := mem_preC.mp hx
    rw [H_eq_centralizer, centralizer_quotW_eq_map hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC] at hxw
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxw
    have hyH : (y : G) ∈ H z := Subgroup.mem_subgroupOf.mp hy
    have h1 := exists_zpowers_of_quotMk_eq hxC y.2 hyx.symm
    have h2 : (y : G)⁻¹ * x ∈ H z :=
      J_le_H (zpowers_le_J_of_mem_centerIn hs.hz₁ h1)
    have h3 : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [h3]
    exact Subgroup.mul_mem _ hyH h2
  · intro hx
    exact mem_preC.mpr ⟨H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ hx,
      quotH_mem_H hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC ⟨x, hx⟩⟩

theorem preC_J_quotW (hs : QuotSetup z z₁) : preC z₁ (J (quotW hs.hzC)) = J z := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxC, hxw⟩ := mem_preC.mp hx
    obtain ⟨y, hyJ, hyx⟩ := (mem_J_quotW_iff hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC _).mp hxw
    have h1 := exists_zpowers_of_quotMk_eq hxC (H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ y.2)
      hyx.symm
    have h2 : (y : G)⁻¹ * x ∈ J z := zpowers_le_J_of_mem_centerIn hs.hz₁ h1
    have h3 : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [h3]
    exact Subgroup.mul_mem _ hyJ h2
  · intro hx
    have hxH : x ∈ H z := J_le_H hx
    exact mem_preC.mpr ⟨H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ hxH,
      (mem_J_quotW_iff hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC _).mpr ⟨⟨x, hxH⟩, hx, rfl⟩⟩

omit [Finite G] in
theorem mem_normalizer_preC_iff (S : Subgroup (QuotC z₁)) {n : G}
    (hn : n ∈ Subgroup.centralizer ({z₁} : Set G)) :
    n ∈ Subgroup.normalizer (preC z₁ S : Set G) ↔
      quotMk z₁ ⟨n, hn⟩ ∈ Subgroup.normalizer (S : Set (QuotC z₁)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hN s
    obtain ⟨y, rfl⟩ := quotMk_surjective z₁ s
    have h1 := hN (y : G)
    have hnyn : n * (y : G) * n⁻¹ ∈ Subgroup.centralizer ({z₁} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hn y.2) (Subgroup.inv_mem _ hn)
    have e : quotMk z₁ ⟨n, hn⟩ * quotMk z₁ y * (quotMk z₁ ⟨n, hn⟩)⁻¹ =
        quotMk z₁ ⟨n * (y : G) * n⁻¹, hnyn⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    constructor
    · intro hy
      exact (mem_preC.mp (h1.mp (mem_preC.mpr ⟨y.2, hy⟩))).2
    · intro hy
      have := h1.mpr (mem_preC.mpr ⟨hnyn, hy⟩)
      exact (mem_preC.mp this).2
  · intro hN g
    by_cases hg : g ∈ Subgroup.centralizer ({z₁} : Set G)
    · have hngn : n * g * n⁻¹ ∈ Subgroup.centralizer ({z₁} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hg) (Subgroup.inv_mem _ hn)
      have e : quotMk z₁ ⟨n, hn⟩ * quotMk z₁ ⟨g, hg⟩ * (quotMk z₁ ⟨n, hn⟩)⁻¹ =
          quotMk z₁ ⟨n * g * n⁻¹, hngn⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      have h1 := hN (quotMk z₁ ⟨g, hg⟩)
      rw [e] at h1
      constructor
      · intro hgm
        exact mem_preC.mpr ⟨hngn, h1.mp (mem_preC.mp hgm).2⟩
      · intro hgm
        exact mem_preC.mpr ⟨hg, h1.mpr (mem_preC.mp hgm).2⟩
    · have hngn : n * g * n⁻¹ ∉ Subgroup.centralizer ({z₁} : Set G) := fun hc => hg (by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hc) hn
        simpa [mul_assoc] using this)
      exact ⟨fun hgm => absurd (preC_le_centralizer S hgm) hg,
        fun hgm => absurd (preC_le_centralizer S hgm) hngn⟩

omit [Finite G] in
theorem z₁_ne_one (hs : QuotSetup z z₁) : z₁ ≠ 1 := by
  intro h1
  exact hs.hz₁z (h1 ▸ Subgroup.one_mem _)

theorem not_isConj_z_mul_z₁ (hs : QuotSetup z z₁) : ¬ IsConj z (z * z₁) := fun hc => by
  have hze : z * z₁ ∈ centerIn (J z) := Subgroup.mul_mem _ (z_mem_centerIn_J hs.h) hs.hz₁
  have h1 := eq_of_isConj_of_mem_centerIn_J hs.h hs.hZ (z_mem_centerIn_J hs.h) hze hc
  exact z₁_ne_one hs (mul_left_cancel (a := z) (h1.symm.trans (mul_one z).symm))

theorem not_centralizer_sup_pPrimeCore_quotW (hs : QuotSetup z z₁)
    (hfuse : ∃ g ∈ Subgroup.centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) :
    ¬ (Subgroup.centralizer ({quotW hs.hzC} : Set (QuotC z₁)) ⊔ pPrimeCore 2 (QuotC z₁) = ⊤) := by
  intro hsup
  have hee : z₁ * z₁ = 1 := by
    have h1 := pow_orderOf_eq_one z₁
    rwa [hs.hz₁2, pow_two] at h1
  obtain ⟨g', hg', hgH, hgne⟩ := hfuse
  have hcomm : (g' * z * g'⁻¹) * z = z * (g' * z * g'⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hgH
  have hcommK : (quotMk z₁ ⟨g', hg'⟩ * quotW hs.hzC * (quotMk z₁ ⟨g', hg'⟩)⁻¹) * quotW hs.hzC =
      quotW hs.hzC * (quotMk z₁ ⟨g', hg'⟩ * quotW hs.hzC * (quotMk z₁ ⟨g', hg'⟩)⁻¹) := by
    have h1 : quotMk z₁ (((⟨g', hg'⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z, hs.hzC⟩ *
        ⟨g', hg'⟩⁻¹) * ⟨z, hs.hzC⟩) = quotMk z₁ (⟨z, hs.hzC⟩ * (⟨g', hg'⟩ * ⟨z, hs.hzC⟩ *
        ⟨g', hg'⟩⁻¹)) := congrArg (quotMk z₁) (Subtype.ext hcomm)
    simp only [map_mul, map_inv] at h1
    exact h1
  have h2 := eq_of_commute_of_sup_pPrimeCore_eq_top
    (orderOf_quotW hs.h hs.hz₁z hs.hz₁2 hs.hzC) hsup (quotMk z₁ ⟨g', hg'⟩) hcommK
  have h3 : quotMk z₁ ((⟨g', hg'⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z, hs.hzC⟩ *
      ⟨g', hg'⟩⁻¹) = quotMk z₁ ⟨z, hs.hzC⟩ := by
    rw [map_mul, map_mul, map_inv]
    exact h2
  have h3' : (QuotientGroup.mk ((⟨g', hg'⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) *
      ⟨z, hs.hzC⟩ * ⟨g', hg'⟩⁻¹) : QuotC z₁) = QuotientGroup.mk ⟨z, hs.hzC⟩ := h3
  have h4 := QuotientGroup.eq.mp h3'
  have h6 : (g' * z * g'⁻¹)⁻¹ * z ∈ Subgroup.zpowers z₁ := Subgroup.mem_subgroupOf.mp h4
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hs.hz₁2 h6 with h7 | h7
  · exact hgne (inv_mul_eq_one.mp h7)
  · have h8 : z = (g' * z * g'⁻¹) * z₁ := inv_mul_eq_iff_eq_mul.mp h7
    have h9 : g' * z * g'⁻¹ = z * z₁ := by
      have h10 : (g' * z * g'⁻¹) * z₁ * z₁ = z * z₁ := by rw [← h8]
      calc g' * z * g'⁻¹ = (g' * z * g'⁻¹) * (z₁ * z₁) := by rw [hee, mul_one]
        _ = (g' * z * g'⁻¹) * z₁ * z₁ := (mul_assoc _ _ _).symm
        _ = z * z₁ := h10
    exact not_isConj_z_mul_z₁ hs (isConj_iff.mpr ⟨g', h9⟩)

theorem comm_mem_of_index_two {K : Type*} [Group K] {K₁ : Subgroup K} (hK₁ : K₁.index = 2)
    (a b : K) : ⁅a, b⁆ ∈ K₁ := by
  rw [commutatorElement_def]
  simp only [Subgroup.mul_mem_iff_of_index_two hK₁, inv_mem_iff]
  tauto

omit [Finite G] in
theorem commutator_mem_centralizer {a b : G} (ha : a ∈ Subgroup.centralizer ({z₁} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z₁} : Set G)) :
    ⁅a, b⁆ ∈ Subgroup.centralizer ({z₁} : Set G) := by
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
    (Subgroup.inv_mem _ hb)

theorem commutator_H_le_preC {K₁ : Subgroup (QuotC z₁)} (hs : QuotSetup z z₁)
    (hK₁ : K₁.index = 2) : ⁅H z, H z⁆ ≤ preC z₁ K₁ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haC := H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ ha
  have hbC := H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ hb
  have hab := commutator_mem_centralizer haC hbC
  refine mem_preC.mpr ⟨hab, ?_⟩
  have : quotMk z₁ ⟨⁅a, b⁆, hab⟩ = ⁅quotMk z₁ ⟨a, haC⟩, quotMk z₁ ⟨b, hbC⟩⁆ := by
    rw [← map_commutatorElement]
    rfl
  rw [this]
  exact comm_mem_of_index_two hK₁ _ _

theorem z_mem_preC_of_index_two {K₁ : Subgroup (QuotC z₁)} (hs : QuotSetup z z₁)
    (hK₁ : K₁.index = 2) : z ∈ preC z₁ K₁ := by
  have h1 : z ∈ ⁅J z, J z⁆ := by
    rw [show ⁅J z, J z⁆ = Subgroup.zpowers z from hs.h.2.2.1]
    exact Subgroup.mem_zpowers z
  exact commutator_H_le_preC hs hK₁
    (Subgroup.commutator_mono (J_le_H (z := z)) (J_le_H (z := z)) h1)

theorem J_le_preC_of_index_two (hs : QuotSetup z z₁)
    (hJ' : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z)) {K₁ : Subgroup (QuotC z₁)}
    (hK₁ : K₁.index = 2) : J z ≤ preC z₁ K₁ := by
  have hZJ : centerIn (J z) ≤ preC z₁ K₁ := by
    intro c hc
    rcases (mem_centerIn_J_iff hs.h hs.hz₁ hs.hz₁z hs.hz₁2).mp hc with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact z_mem_preC_of_index_two hs hK₁
    · exact z₁_mem_preC K₁
    · exact Subgroup.mul_mem _ (z_mem_preC_of_index_two hs hK₁) (z₁_mem_preC K₁)
  exact hJ'.trans (sup_le (commutator_H_le_preC hs hK₁) hZJ)

omit [Finite G] in
theorem closure_mul_comm_and_sq {S : Set G} (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a * a = 1) :
    (∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) ∧
      ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  have h1 : ∀ a ∈ S, ∀ y ∈ Subgroup.closure S, y * a = a * y := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx a ha
    | one => simp
    | mul x y _ _ hx hy =>
      calc x * y * a = x * (y * a) := mul_assoc _ _ _
        _ = x * (a * y) := by rw [hy]
        _ = (x * a) * y := (mul_assoc _ _ _).symm
        _ = (a * x) * y := by rw [hx]
        _ = a * (x * y) := mul_assoc _ _ _
    | inv x _ hx =>
      calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * a) * x⁻¹ := by rw [← hx]
        _ = a * x⁻¹ := by group
  have h2 : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction generalizing y with
    | mem a ha => exact (h1 a ha y hy).symm
    | one => simp
    | mul a b _ _ ha hb =>
      calc a * b * y = a * (b * y) := mul_assoc _ _ _
        _ = a * (y * b) := by rw [hb y hy]
        _ = (a * y) * b := (mul_assoc _ _ _).symm
        _ = (y * a) * b := by rw [ha y hy]
        _ = y * (a * b) := mul_assoc _ _ _
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by
            have : a⁻¹ * y = a⁻¹ * y * (a * a⁻¹) := by group
            calc a⁻¹ * y = a⁻¹ * y * (a * a⁻¹) := this
              _ = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [← ha y hy]
        _ = y * a⁻¹ := by group
  refine ⟨h2, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem a ha => exact hsq a ha
  | one => simp
  | mul a b ha hb ha2 hb2 =>
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [h2 b hb a ha]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, mul_one]
  | inv a ha ha2 =>
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [ha2, inv_one]

theorem isElemAbelian_preC (hs : QuotSetup z z₁) {Ek : Subgroup (QuotC z₁)}
    (hwE : quotW hs.hzC ∈ Ek) (hEH : Ek ≤ H (quotW hs.hzC))
    (hgen : ∀ x ∈ Ek, x ∈ Subgroup.closure
      {y : QuotC z₁ | ∃ n ∈ Subgroup.normalizer (Ek : Set (QuotC z₁)),
        y = n * quotW hs.hzC * n⁻¹}) :
    IsElemAbelian 2 (preC z₁ Ek) := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hs.h.1, pow_two] at this
  have hz₁2 : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hs.hz₁2, pow_two] at this
  have hEH' : preC z₁ Ek ≤ H z := (preC_mono hEH).trans (preC_H_quotW hs).le
  have hzE : z ∈ preC z₁ Ek := mem_preC.mpr ⟨hs.hzC, hwE⟩
  let Gens : Set G := {y | ∃ n ∈ Subgroup.centralizer ({z₁} : Set G),
      n ∈ Subgroup.normalizer (preC z₁ Ek : Set G) ∧ y = n * z * n⁻¹}
  have hGE : ∀ y ∈ Gens, y ∈ preC z₁ Ek := by
    rintro y ⟨n, hn, hnN, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hnN z).mp hzE
  have hGsq : ∀ y ∈ Gens, y * y = 1 := by
    rintro y ⟨n, hn, hnN, rfl⟩
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hGcomm : ∀ a ∈ Gens, ∀ b ∈ Gens, a * b = b * a := by
    rintro a ⟨n₁, hn₁, hn₁N, rfl⟩ b ⟨n₂, hn₂, hn₂N, rfl⟩
    have hm : n₁⁻¹ * n₂ ∈ Subgroup.normalizer (preC z₁ Ek : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁N) hn₂N
    have hz' : (n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹ ∈ preC z₁ Ek :=
      (Subgroup.mem_normalizer_iff.mp hm z).mp hzE
    have hz'H : (n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹ ∈ H z := hEH' hz'
    have hc : ((n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹) * z =
        z * ((n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hz'H
    calc n₁ * z * n₁⁻¹ * (n₂ * z * n₂⁻¹)
        = n₁ * (z * ((n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹)) * n₁⁻¹ := by group
      _ = n₁ * (((n₁⁻¹ * n₂) * z * (n₁⁻¹ * n₂)⁻¹) * z) * n₁⁻¹ := by rw [hc]
      _ = n₂ * z * n₂⁻¹ * (n₁ * z * n₁⁻¹) := by group
  have hGC : ∀ y ∈ Gens, y ∈ Subgroup.centralizer ({z₁} : Set G) :=
    fun y hy => preC_le_centralizer _ (hGE y hy)
  let S : Set G := Gens ∪ {z₁}
  have hSsq : ∀ a ∈ S, a * a = 1 := by
    rintro a (ha | ha)
    · exact hGsq a ha
    · rw [Set.mem_singleton_iff.mp ha]
      exact hz₁2
  have hScomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hGcomm a ha b hb
    · rw [Set.mem_singleton_iff.mp hb]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hGC a ha)
    · rw [Set.mem_singleton_iff.mp ha]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hGC b hb)).symm
    · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
  obtain ⟨hYcomm, hYsq⟩ := closure_mul_comm_and_sq hScomm hSsq
  have hz₁Y : z₁ ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hGY : ∀ y ∈ Gens, y ∈ Subgroup.closure S := fun y hy => Subgroup.subset_closure (Or.inl hy)
  let Q : Subgroup (QuotC z₁) :=
    ((Subgroup.closure S).comap (Subgroup.centralizer ({z₁} : Set G)).subtype).map (quotMk z₁)
  have hTQ : Subgroup.closure {y : QuotC z₁ | ∃ n ∈ Subgroup.normalizer (Ek : Set (QuotC z₁)),
      y = n * quotW hs.hzC * n⁻¹} ≤ Q := by
    rw [Subgroup.closure_le]
    rintro y ⟨nbar, hnbar, rfl⟩
    obtain ⟨n, rfl⟩ := quotMk_surjective z₁ nbar
    have hnN : (n : G) ∈ Subgroup.normalizer (preC z₁ Ek : Set G) :=
      (mem_normalizer_preC_iff Ek n.2).mpr hnbar
    have hg : (n : G) * z * (n : G)⁻¹ ∈ Gens := ⟨n, n.2, hnN, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨(n : G) * z * (n : G)⁻¹, hGC _ hg⟩, hGY _ hg, ?_⟩
    have e : (⟨(n : G) * z * (n : G)⁻¹, hGC _ hg⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
        n * ⟨z, hs.hzC⟩ * n⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hEY : preC z₁ Ek ≤ Subgroup.closure S := by
    intro x hx
    obtain ⟨hxC, hxE⟩ := mem_preC.mp hx
    have h1 : quotMk z₁ ⟨x, hxC⟩ ∈ Q := hTQ (hgen _ hxE)
    obtain ⟨y', hy'Y, hy'x⟩ := Subgroup.mem_map.mp h1
    have h2 := exists_zpowers_of_quotMk_eq hxC y'.2 hy'x.symm
    have h3 : x = (y' : G) * ((y' : G)⁻¹ * x) := by group
    rw [h3]
    exact Subgroup.mul_mem _ hy'Y ((Subgroup.zpowers_le.mpr hz₁Y) h2)
  refine ⟨isMulCommutative_iff.mpr (fun a b => Subtype.ext (hYcomm _ (hEY a.2) _ (hEY b.2))), ?_⟩
  intro x hx
  rw [pow_two]
  exact hYsq x (hEY hx)

theorem preC_le_commutator_sup_J (hs : QuotSetup z z₁) {Ek : Subgroup (QuotC z₁)}
    (h : Ek ≤ ⁅H (quotW hs.hzC), H (quotW hs.hzC)⁆ ⊔ J (quotW hs.hzC)) :
    preC z₁ Ek ≤ ⁅H z, H z⁆ ⊔ J z := by
  set T : Subgroup G := ⁅H z, H z⁆ ⊔ J z with hT
  set Q : Subgroup (QuotC z₁) :=
    (T.comap (Subgroup.centralizer ({z₁} : Set G)).subtype).map (quotMk z₁) with hQ
  have hHH : ⁅H (quotW hs.hzC), H (quotW hs.hzC)⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, hx, hxa⟩ := exists_mem_preC_of_mem ha
    obtain ⟨y, hy, hyb⟩ := exists_mem_preC_of_mem hb
    have hxH : x ∈ H z := by rw [← preC_H_quotW hs]; exact hx
    have hyH : y ∈ H z := by rw [← preC_H_quotW hs]; exact hy
    have hxC := preC_le_centralizer _ hx
    have hyC := preC_le_centralizer _ hy
    have hxy := commutator_mem_centralizer hxC hyC
    have hxyT : ⁅x, y⁆ ∈ T :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hxH hyH)
    refine Subgroup.mem_map.mpr ⟨⟨⁅x, y⁆, hxy⟩, hxyT, ?_⟩
    rw [← hxa, ← hyb, ← map_commutatorElement]
    rfl
  have hJJ : J (quotW hs.hzC) ≤ Q := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := exists_mem_preC_of_mem ha
    have hxJ : x ∈ J z := by rw [← preC_J_quotW hs]; exact hx
    refine Subgroup.mem_map.mpr ⟨⟨x, preC_le_centralizer _ hx⟩, Subgroup.mem_sup_right hxJ, hxa⟩
  intro x hx
  obtain ⟨hxC, hxE⟩ := mem_preC.mp hx
  obtain ⟨y', hy'T, hy'x⟩ := Subgroup.mem_map.mp ((sup_le hHH hJJ) (h hxE))
  have h2 := exists_zpowers_of_quotMk_eq hxC y'.2 hy'x.symm
  have hz₁T : z₁ ∈ T := Subgroup.mem_sup_right hs.hz₁.1
  have h3 : x = (y' : G) * ((y' : G)⁻¹ * x) := by group
  rw [h3]
  exact Subgroup.mul_mem _ hy'T ((Subgroup.zpowers_le.mpr hz₁T) h2)

theorem centerIn_le_preC (hs : QuotSetup z z₁) {Ek : Subgroup (QuotC z₁)}
    (hwE : quotW hs.hzC ∈ Ek) : centerIn (J z) ≤ preC z₁ Ek := by
  intro c hc
  rcases (mem_centerIn_J_iff hs.h hs.hz₁ hs.hz₁z hs.hz₁2).mp hc with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact mem_preC.mpr ⟨hs.hzC, hwE⟩
  · exact z₁_mem_preC Ek
  · exact Subgroup.mul_mem _ (mem_preC.mpr ⟨hs.hzC, hwE⟩) (z₁_mem_preC Ek)

theorem preC_inf_J (hs : QuotSetup z z₁) (Ek : Subgroup (QuotC z₁)) :
    preC z₁ Ek ⊓ J z = preC z₁ (Ek ⊓ J (quotW hs.hzC)) := by
  rw [preC_inf, preC_J_quotW hs]

theorem relIndex_normalizer_preC (hs : QuotSetup z z₁) (Ek : Subgroup (QuotC z₁)) :
    (preC z₁ Ek).relIndex (Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ H z) =
      Ek.relIndex (Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ H (quotW hs.hzC)) := by
  have h1 : Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ H z =
      preC z₁ (Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ H (quotW hs.hzC)) := by
    ext x
    constructor
    · rintro ⟨hxN, hxH⟩
      have hxC := H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ hxH
      exact mem_preC.mpr ⟨hxC, (mem_normalizer_preC_iff Ek hxC).mp hxN,
        quotH_mem_H hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC ⟨x, hxH⟩⟩
    · intro hx
      obtain ⟨hxC, hxN, hxHw⟩ := mem_preC.mp hx
      refine ⟨(mem_normalizer_preC_iff Ek hxC).mpr hxN, ?_⟩
      have : x ∈ preC z₁ (H (quotW hs.hzC)) := mem_preC.mpr ⟨hxC, hxHw⟩
      rwa [preC_H_quotW hs] at this
  rw [h1, relIndex_preC]

theorem preC_eq_H_inf_centralizer (hs : QuotSetup z z₁) {Ek : Subgroup (QuotC z₁)}
    (hab : IsElemAbelian 2 (preC z₁ Ek))
    (hECE : Ek = H (quotW hs.hzC) ⊓ Subgroup.centralizer
      ((Ek ⊓ J (quotW hs.hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁))) :
    preC z₁ Ek = H z ⊓ Subgroup.centralizer ((preC z₁ Ek ⊓ J z : Subgroup G) : Set G) := by
  have hEH : preC z₁ Ek ≤ H z := by
    have : Ek ≤ H (quotW hs.hzC) := hECE ▸ inf_le_left
    exact (preC_mono this).trans (preC_H_quotW hs).le
  ext x
  constructor
  · intro hx
    refine ⟨hEH hx, Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_)⟩
    exact @Subgroup.mul_comm_of_mem_isMulCommutative G _ (preC z₁ Ek) hab.1 _ _ hy.1 hx
  · rintro ⟨hxH, hxc⟩
    have hxC := H_le_centralizer_of_mem_centerIn hs.hZ hs.hz₁ hxH
    refine mem_preC.mpr ⟨hxC, ?_⟩
    have h1 : quotMk z₁ ⟨x, hxC⟩ ∈ H (quotW hs.hzC) ⊓ Subgroup.centralizer
        ((Ek ⊓ J (quotW hs.hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁)) := by
      refine ⟨quotH_mem_H hs.h hs.hZ hs.hz₁ hs.hz₁z hs.hz₁2 hs.hzC ⟨x, hxH⟩,
        Subgroup.mem_centralizer_iff.mpr (fun a ha => ?_)⟩
      obtain ⟨y, hy, hya⟩ := exists_mem_preC_of_mem (S := Ek ⊓ J (quotW hs.hzC)) ha
      have hyEJ : y ∈ preC z₁ Ek ⊓ J z := by rw [preC_inf_J hs]; exact hy
      have hxy := Subgroup.mem_centralizer_iff.mp hxc y hyEJ
      rw [← hya]
      have := congrArg (quotMk z₁) (Subtype.ext hxy : (⟨y, preC_le_centralizer _ hy⟩ :
        ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨x, hxC⟩ =
          ⟨x, hxC⟩ * ⟨y, preC_le_centralizer _ hy⟩)
      rw [map_mul, map_mul] at this
      exact this
    rw [← hECE] at h1
    exact h1

theorem isParrottE_preC (hs : QuotSetup z z₁) {Ek : Subgroup (QuotC z₁)}
    (hEH : Ek ≤ H (quotW hs.hzC))
    (hEHJ : Ek ≤ ⁅H (quotW hs.hzC), H (quotW hs.hzC)⁆ ⊔ J (quotW hs.hzC))
    (hwE : quotW hs.hzC ∈ Ek) (hcard : Nat.card Ek = 2 ^ 9)
    (hcardJ : Nat.card ↥(Ek ⊓ J (quotW hs.hzC)) = 2 ^ 5)
    (hECE : Ek = H (quotW hs.hzC) ⊓ Subgroup.centralizer
      ((Ek ⊓ J (quotW hs.hzC) : Subgroup (QuotC z₁)) : Set (QuotC z₁)))
    (hrel : Ek.relIndex (Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ H (quotW hs.hzC)) = 1920)
    (hgen : ∀ x ∈ Ek, x ∈ Subgroup.closure
      {y : QuotC z₁ | ∃ n ∈ Subgroup.normalizer (Ek : Set (QuotC z₁)),
        y = n * quotW hs.hzC * n⁻¹}) :
    IsParrottE z (preC z₁ Ek) := by
  have hab := isElemAbelian_preC hs hwE hEH hgen
  unfold IsParrottE
  refine ⟨(preC_mono hEH).trans (preC_H_quotW hs).le, preC_le_commutator_sup_J hs hEHJ,
    centerIn_le_preC hs hwE, hab, ?_, ?_, preC_eq_H_inf_centralizer hs hab hECE, ?_⟩
  · rw [card_preC hs.hz₁2, hcard]
    norm_num
  · rw [preC_inf_J hs, card_preC hs.hz₁2, hcardJ]
    norm_num
  · rw [relIndex_normalizer_preC hs, hrel]

theorem eq_normalizer_inf_of_index_two {K : Type*} [Group K] [Finite K]
    {Ek Kp K₁ Hw Hw' : Subgroup K} (hK₁ : K₁.index = 2) (hEK₁ : Ek ≤ K₁)
    (hEKp : Ek ≤ Kp)
    (hKpM : Kp ≤ Subgroup.normalizer (Ek : Set K))
    (hKpi : Kp.relIndex (Subgroup.normalizer (Ek : Set K)) = 2)
    (hQ : ∀ L : Subgroup K, Ek ≤ L → L ≤ Kp → L.relIndex Kp ≠ 2)
    (hK₁H : K₁ ⊓ Hw ≤ Hw') (hMH' : Subgroup.normalizer (Ek : Set K) ⊓ Hw' ≤ Kp)
    (hNH : ¬ (Subgroup.normalizer (Ek : Set K) ⊓ Hw ≤ Kp)) :
    Kp = Subgroup.normalizer (Ek : Set K) ⊓ K₁ := by
  have hKpK₁ : Kp ≤ K₁ := by
    refine CFSG.GroupTheory.le_of_relIndex_two_of_forall_relIndex_ne_two
      (N := ⊤) le_top ?_ hEK₁ hEKp hQ
    rwa [Subgroup.relIndex_top_right]
  have hnotM : ¬ Subgroup.normalizer (Ek : Set K) ≤ K₁ := by
    intro hM
    apply hNH
    intro x hx
    exact hMH' ⟨hx.1, hK₁H ⟨hM hx.1, hx.2⟩⟩
  have hK₁n : K₁.Normal := Subgroup.normal_of_index_eq_two hK₁
  have h1 : (Subgroup.normalizer (Ek : Set K) ⊓ K₁).relIndex
      (Subgroup.normalizer (Ek : Set K)) = 2 := by
    rw [Subgroup.inf_relIndex_left]
    have h2 : K₁.relIndex (Subgroup.normalizer (Ek : Set K)) ∣ K₁.index :=
      Subgroup.relIndex_dvd_index_of_normal K₁ _
    rw [hK₁] at h2
    have h3 : K₁.relIndex (Subgroup.normalizer (Ek : Set K)) ≠ 1 := by
      rwa [Ne, Subgroup.relIndex_eq_one]
    have h4 := Nat.le_of_dvd (by norm_num) h2
    have h0 : K₁.relIndex (Subgroup.normalizer (Ek : Set K)) ≠ 0 := by
      intro h0
      rw [h0] at h2
      omega
    omega
  have h4 := Subgroup.relIndex_mul_relIndex Kp (Subgroup.normalizer (Ek : Set K) ⊓ K₁)
    (Subgroup.normalizer (Ek : Set K)) (le_inf hKpM hKpK₁) inf_le_left
  rw [hKpi, h1] at h4
  have h5 : Kp.relIndex (Subgroup.normalizer (Ek : Set K) ⊓ K₁) = 1 := by omega
  exact le_antisymm (le_inf hKpM hKpK₁) (Subgroup.relIndex_eq_one.mp h5)

omit [Finite G] in
theorem preC_quotient_equiv (S : Subgroup (QuotC z₁)) :
    ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (preC z₁ S)).Normal),
      Nonempty (↥(preC z₁ S) ⧸ (Subgroup.zpowers z₁).subgroupOf (preC z₁ S) ≃* ↥S) := by
  let θ₀ : ↥(preC z₁ S) →* QuotC z₁ :=
    (quotMk z₁).comp (Subgroup.inclusion (preC_le_centralizer S))
  let θ : ↥(preC z₁ S) →* ↥S := θ₀.codRestrict S (fun x => quotMk_mem_of_mem_preC x.2)
  have hθs : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    obtain ⟨x, hx, hxs⟩ := exists_mem_preC_of_mem hs
    exact ⟨⟨x, hx⟩, Subtype.ext hxs⟩
  have hker : θ.ker = (Subgroup.zpowers z₁).subgroupOf (preC z₁ S) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : quotMk z₁ ⟨(x : G), preC_le_centralizer S x.2⟩ = 1 := congrArg Subtype.val h1
      exact (mem_ker_quotMk_iff ⟨(x : G), preC_le_centralizer S x.2⟩).mp h2
    · intro h1
      apply Subtype.ext
      exact (mem_ker_quotMk_iff (z₁ := z₁) ⟨(x : G), preC_le_centralizer S x.2⟩).mpr h1
  have hN : ((Subgroup.zpowers z₁).subgroupOf (preC z₁ S)).Normal := hker ▸ θ.normal_ker
  refine ⟨hN, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθs)

omit [Finite G] in
theorem normalizer_inf_preC_quotient_equiv (Ek K₁ Kp : Subgroup (QuotC z₁))
    (hKp : Kp = Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ K₁)
    [hN : (Ek.subgroupOf Kp).Normal] :
    ∃ (_ : ((preC z₁ Ek).subgroupOf
        (Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁)).Normal),
      Nonempty (↥(Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁) ⧸
        (preC z₁ Ek).subgroupOf (Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁) ≃*
        (↥Kp ⧸ Ek.subgroupOf Kp)) := by
  set D : Subgroup G := Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁ with hD
  have hDC : D ≤ Subgroup.centralizer ({z₁} : Set G) := inf_le_right.trans (preC_le_centralizer _)
  have hmem : ∀ x : ↥D, quotMk z₁ (Subgroup.inclusion hDC x) ∈ Kp := by
    intro x
    have hxC : (x : G) ∈ Subgroup.centralizer ({z₁} : Set G) := hDC x.2
    rw [hKp]
    exact ⟨(mem_normalizer_preC_iff Ek hxC).mp x.2.1, quotMk_mem_of_mem_preC x.2.2⟩
  let ρ₀ : ↥D →* ↥Kp := ((quotMk z₁).comp (Subgroup.inclusion hDC)).codRestrict Kp hmem
  let ρ : ↥D →* ↥Kp ⧸ Ek.subgroupOf Kp :=
    (QuotientGroup.mk' (Ek.subgroupOf Kp) (nN := hN)).comp ρ₀
  have hρs : Function.Surjective ρ := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : (k : QuotC z₁) ∈ Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ K₁ := hKp ▸ k.2
    obtain ⟨x, hx, hxk⟩ := exists_mem_preC_of_mem hk.2
    have hxC := preC_le_centralizer _ hx
    have hxN : x ∈ Subgroup.normalizer (preC z₁ Ek : Set G) :=
      (mem_normalizer_preC_iff Ek hxC).mpr (by rw [hxk]; exact hk.1)
    have hxk' : ρ₀ ⟨x, hxN, hx⟩ = k := Subtype.ext hxk
    refine ⟨⟨x, hxN, hx⟩, ?_⟩
    show (QuotientGroup.mk' (Ek.subgroupOf Kp)) (ρ₀ ⟨x, hxN, hx⟩) = QuotientGroup.mk k
    rw [hxk']
    rfl
  have hker : ρ.ker = (preC z₁ Ek).subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h2 : ρ₀ x ∈ Ek.subgroupOf Kp := (QuotientGroup.eq_one_iff _).mp h1
      exact mem_preC.mpr ⟨hDC x.2, Subgroup.mem_subgroupOf.mp h2⟩
    · intro h1
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      exact (mem_preC.mp h1).2
  have hN' : ((preC z₁ Ek).subgroupOf D).Normal := hker ▸ ρ.normal_ker
  refine ⟨hN', ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)

omit [Finite G] in
theorem preC_top (z₁ : G) : preC z₁ ⊤ = Subgroup.centralizer ({z₁} : Set G) := by
  ext x
  constructor
  · intro hx
    exact (mem_preC.mp hx).1
  · intro hx
    exact mem_preC.mpr ⟨hx, Subgroup.mem_top _⟩

omit [Finite G] in
theorem relIndex_preC_centralizer (S : Subgroup (QuotC z₁)) :
    (preC z₁ S).relIndex (Subgroup.centralizer ({z₁} : Set G)) = S.index := by
  have h1 := relIndex_preC S ⊤
  rw [preC_top z₁, Subgroup.relIndex_top_right] at h1
  exact h1

theorem quotMk_mem_zpowers_of_mem_centerIn (hs : QuotSetup z z₁) {y : G}
    (hy : y ∈ centerIn (J z)) (hyC : y ∈ Subgroup.centralizer ({z₁} : Set G)) :
    quotMk z₁ ⟨y, hyC⟩ ∈ Subgroup.zpowers (quotW hs.hzC) := by
  have hz₁1 : quotMk z₁ ⟨z₁, z₁_mem_centralizer z₁⟩ = 1 :=
    (mem_ker_quotMk_iff _).mpr (Subgroup.mem_zpowers z₁)
  rcases (mem_centerIn_J_iff hs.h hs.hz₁ hs.hz₁z hs.hz₁2).mp hy with rfl | rfl | rfl | rfl
  · have : (⟨(1 : G), hyC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = 1 := rfl
    rw [this, map_one]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _
  · rw [hz₁1]
    exact Subgroup.one_mem _
  · have : (⟨z * z₁, hyC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
        ⟨z, hs.hzC⟩ * ⟨z₁, z₁_mem_centralizer z₁⟩ := rfl
    rw [this, map_mul, hz₁1, mul_one]
    exact Subgroup.mem_zpowers _

theorem orderOf_eq_two_of_mem_centerIn_J (h : Tim79a.ParrottHyp z) {e : G}
    (he : e ∈ centerIn (J z)) (he1 : e ≠ 1) (hez : e ≠ z) : orderOf e = 2 := by
  obtain ⟨z₁, hz₁c, hz₁z, hz₁2⟩ := exists_z1 h
  have hz₁ : z₁ ∈ centerIn (J z) := by
    rw [hz₁c]
    exact (le_sup_right : Subgroup.zpowers z₁ ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers z₁)
      (Subgroup.mem_zpowers z₁)
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hz₁2).mp he with rfl | rfl | rfl | rfl
  · exact absurd rfl he1
  · exact absurd rfl hez
  · exact hz₁2
  · exact (exists_z1_mul h hz₁ hz₁z hz₁2).2.2

theorem quotH_eq_iff (hZ : centerIn (J z) = centerIn (H z)) (hz₁ : z₁ ∈ centerIn (J z))
    (x y : ↥(H z)) :
    quotH hZ hz₁ x = quotH hZ hz₁ y ↔ (x : G)⁻¹ * (y : G) ∈ Subgroup.zpowers z₁ := by
  have h1 := mem_ker_quotH_iff hZ hz₁ (x⁻¹ * y)
  have e : (((x⁻¹ * y : ↥(H z)) : G)) = (x : G)⁻¹ * (y : G) := rfl
  rw [e, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem hB3_of_lemma32 (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hL32 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∀ j ∈ J w, orderOf j = 2 → j ∉ Subgroup.zpowers w → ¬ IsConj w j) :
    ∀ e ∈ centerIn (J z), e ≠ 1 → e ≠ z →
      (∃ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z →
        ∀ g ∈ centralizer ({e} : Set G), g * z * g⁻¹ ≠ j := by
  intro e he he1 hez hfuse j hj hj2 hjz g hg hgj
  have hz2 : orderOf z = 2 := h.1
  have hord : orderOf e = 2 := orderOf_eq_two_of_mem_centerIn_J h he he1 hez
  have hee : e * e = 1 := by
    have h1 := pow_orderOf_eq_one e
    rwa [hord, pow_two] at h1
  have hezp : e ∉ Subgroup.zpowers z := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hz2 hm with h1 | h1
    exacts [he1 h1, hez h1]
  have hs : QuotSetup z e := ⟨h, hZ, he, hezp, hord⟩
  have hzC := hs.hzC
  have hA := hs.hA
  have hnot := not_centralizer_sup_pPrimeCore_quotW hs hfuse
  have hnc : ¬ IsConj z (z * e) := not_isConj_z_mul_z₁ hs
  have hnce : ¬ IsConj z e := fun hc =>
    hez (eq_of_isConj_of_mem_centerIn_J h hZ (z_mem_centerIn_J h) he hc).symm
  have hjH : j ∈ H z := J_le_H hj
  have hjj : j * j = 1 := by
    have h1 := pow_orderOf_eq_one j
    rwa [hj2, pow_two] at h1
  have hjJ : quotH hZ he ⟨j, hjH⟩ ∈ J (quotW hzC) :=
    (mem_J_quotW_iff h hZ he hezp hord hzC _).mpr ⟨⟨j, hjH⟩, hj, rfl⟩
  have hj1 : quotH hZ he ⟨j, hjH⟩ ≠ 1 := by
    intro h1
    have h2 : quotH hZ he ⟨j, hjH⟩ = quotH hZ he 1 := by rw [map_one]; exact h1
    have h3 := (quotH_eq_iff hZ he ⟨j, hjH⟩ 1).mp h2
    have h4 : j ∈ Subgroup.zpowers e := by
      have h5 := Subgroup.inv_mem _ h3
      simpa using h5
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hord h4 with h5 | h5
    · rw [h5, orderOf_one] at hj2
      exact absurd hj2 (by norm_num)
    · exact hnce (isConj_iff.mpr ⟨g, hgj.trans h5⟩)
  have hjw : quotH hZ he ⟨j, hjH⟩ ≠ quotW hzC := by
    intro h1
    have h2 : quotH hZ he ⟨j, hjH⟩ = quotH hZ he ⟨z, z_mem_H⟩ := h1
    have h3 := (quotH_eq_iff hZ he ⟨j, hjH⟩ ⟨z, z_mem_H⟩).mp h2
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hord h3 with h5 | h5
    · have h6 : j = z := inv_mul_eq_one.mp h5
      rw [h6] at hjz
      exact hjz (Subgroup.mem_zpowers z)
    · have h8 : z = j * e := inv_mul_eq_iff_eq_mul.mp h5
      have h9 : g * z * g⁻¹ = z * e := by
        rw [hgj]
        calc j = j * (e * e) := by rw [hee, mul_one]
          _ = j * e * e := (mul_assoc _ _ _).symm
          _ = z * e := by rw [← h8]
      exact hnc (isConj_iff.mpr ⟨g, h9⟩)
  have hjord : orderOf (quotH hZ he ⟨j, hjH⟩) = 2 := by
    apply orderOf_eq_prime _ hj1
    rw [pow_two, ← map_mul]
    have : (⟨j, hjH⟩ : ↥(H z)) * ⟨j, hjH⟩ = 1 := Subtype.ext hjj
    rw [this, map_one]
  have hjnot : quotH hZ he ⟨j, hjH⟩ ∉ Subgroup.zpowers (quotW hzC) := by
    intro hm
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two (orderOf_quotW h hezp hord hzC) hm
      with h1 | h1
    exacts [hj1 h1, hjw h1]
  have hconj : IsConj (quotW hzC) (quotH hZ he ⟨j, hjH⟩) := by
    refine isConj_iff.mpr ⟨quotMk e ⟨g, hg⟩, ?_⟩
    have h0 : (⟨g, hg⟩ : ↥(Subgroup.centralizer ({e} : Set G))) * ⟨z, hzC⟩ * ⟨g, hg⟩⁻¹ =
        ⟨j, H_le_centralizer_of_mem_centerIn hZ he hjH⟩ := Subtype.ext hgj
    calc quotMk e ⟨g, hg⟩ * quotW hzC * (quotMk e ⟨g, hg⟩)⁻¹
        = quotMk e ((⟨g, hg⟩ : ↥(Subgroup.centralizer ({e} : Set G))) * ⟨z, hzC⟩ *
            ⟨g, hg⟩⁻¹) := by rw [map_mul, map_mul, map_inv]; rfl
      _ = quotMk e ⟨j, H_le_centralizer_of_mem_centerIn hZ he hjH⟩ := by rw [h0]
      _ = quotH hZ he ⟨j, hjH⟩ := rfl
  exact hL32 (QuotC e) (quotW hzC) hA hnot _ hjJ hjord hjnot hconj

theorem hB2c_of_theorem3 (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    (hJ' : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hT3 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        (∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X)) ∧
        K₁ ⊓ H w ≤ ⁅H w, H w⁆)
    (hL345 : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      ¬ (Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤) →
      ∃ E K' : Subgroup K,
        E ≤ H w ∧ E ≤ ⁅H w, H w⁆ ⊔ J w ∧ w ∈ E ∧
        Nat.card E = 2 ^ 9 ∧ Nat.card ↥(E ⊓ J w) = 2 ^ 5 ∧
        E = H w ⊓ Subgroup.centralizer ((E ⊓ J w : Subgroup K) : Set K) ∧
        E.relIndex (normalizer (E : Set K) ⊓ H w) = 1920 ∧
        (∀ x ∈ E, x ∈ Subgroup.closure
          {y : K | ∃ n ∈ normalizer (E : Set K), y = n * w * n⁻¹}) ∧
        E ≤ K' ∧ K'.relIndex (normalizer (E : Set K)) = 2 ∧
        normalizer (E : Set K) ⊓ ⁅H w, H w⁆ ≤ K' ∧ ¬ (normalizer (E : Set K) ⊓ H w ≤ K') ∧
        ((E.subgroupOf K').Normal ∧ Nat.card (↥K' ⧸ E.subgroupOf K') = 20160 ∧
           ∀ L : Subgroup K, E ≤ L → L ≤ K' → L.relIndex K' ≠ 2) ∧
        ∃ t j₀ : K, t ∈ E ∧ t ∉ J w ∧ orderOf t = 2 ∧ IsConj w t ∧
          j₀ ∈ J w ∧ j₀ ∉ Subgroup.zpowers w ∧ IsConj (t * w) j₀) :
    ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      (∃ g ∈ centralizer ({z₁} : Set G), g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
      ∃ U : Subgroup G, U ≤ centralizer ({z₁} : Set G) ∧
        U.relIndex (centralizer ({z₁} : Set G)) = 2 ∧ J z ≤ U ∧
        (∃ (_ : ((Subgroup.zpowers z₁).subgroupOf U).Normal) (X : Type) (_ : Group X),
          CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥U ⧸ (Subgroup.zpowers z₁).subgroupOf U ≃* X)) ∧
        ∃ E : Subgroup G, IsParrottE z E ∧ E ≤ U ∧
          ((E.subgroupOf (normalizer (E : Set G) ⊓ U)).Normal ∧
             Nat.card (↥(normalizer (E : Set G) ⊓ U) ⧸
               E.subgroupOf (normalizer (E : Set G) ⊓ U)) = 20160 ∧
             ∀ L : Subgroup G, E ≤ L → L ≤ normalizer (E : Set G) ⊓ U →
               L.relIndex (normalizer (E : Set G) ⊓ U) ≠ 2) ∧
          ∃ t' j₀ : G, t' ∈ E ∧ t' ∉ J z ∧ orderOf t' = 2 ∧ IsConj z t' ∧ j₀ ∈ J z ∧
            j₀ ∉ centerIn (J z) ∧ IsConj (t' * z) j₀ := by
  intro z₁ hz₁ hz₁z hz₁2 hfuse
  have hs : QuotSetup z z₁ := ⟨h, hZ, hz₁, hz₁z, hz₁2⟩
  have hnot := not_centralizer_sup_pPrimeCore_quotW hs hfuse
  obtain ⟨K₁, hK₁i, -, ⟨X₁, _, hX₁, ⟨e₁⟩⟩, hK₁H⟩ :=
    hT3 (QuotC z₁) (quotW hs.hzC) hs.hA hnot
  obtain ⟨Ek, Kp, hEH, hEHJ, hwE, hcard, hcardJ, hECE, hrel, hgen, hEKp, hKpi, hMH', hNH,
    ⟨hKpN, hKpcard, hKpQ⟩, t, j₀, htE, htJ, ht2, htc, hj₀J, hj₀w, hj₀c⟩ :=
    hL345 (QuotC z₁) (quotW hs.hzC) hs.hA hnot
  have hK₁n : K₁.Normal := Subgroup.normal_of_index_eq_two hK₁i
  have hwK₁ : quotW hs.hzC ∈ K₁ := (mem_preC.mp (z_mem_preC_of_index_two hs hK₁i)).2
  have hEK₁ : Ek ≤ K₁ := by
    intro x hx
    refine (Subgroup.closure_le K₁).mpr ?_ (hgen x hx)
    rintro y ⟨n, hn, rfl⟩
    exact hK₁n.conj_mem _ hwK₁ n
  have hKpM : Kp ≤ Subgroup.normalizer (Ek : Set (QuotC z₁)) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := hKpN.conj_mem ⟨x, hEKp hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨k, hk⟩
      exact Subgroup.mem_subgroupOf.mp this
    · intro hx
      have h1 := hKpN.conj_mem ⟨k * x * k⁻¹, hEKp hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
        (⟨k, hk⟩⁻¹)
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [mul_assoc] using h2
  have hKp : Kp = Subgroup.normalizer (Ek : Set (QuotC z₁)) ⊓ K₁ :=
    eq_normalizer_inf_of_index_two hK₁i hEK₁ hEKp hKpM hKpi hKpQ hK₁H hMH' hNH
  have hE : IsParrottE z (preC z₁ Ek) :=
    isParrottE_preC hs hEH hEHJ hwE hcard hcardJ hECE hrel hgen
  obtain ⟨hN₁, ⟨eU⟩⟩ := preC_quotient_equiv (z₁ := z₁) K₁
  obtain ⟨hND, ⟨eD⟩⟩ :=
    normalizer_inf_preC_quotient_equiv (z₁ := z₁) Ek K₁ Kp hKp (hN := hKpN)
  have hz2 : orderOf z = 2 := h.1
  obtain ⟨c, hc⟩ := isConj_iff.mp htc
  obtain ⟨g, rfl⟩ := quotMk_surjective z₁ c
  have hgz : (g : G) * z * (g : G)⁻¹ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hs.hzC) (Subgroup.inv_mem _ g.2)
  have hq1 : quotMk z₁ ⟨(g : G) * z * (g : G)⁻¹, hgz⟩ = t := by
    rw [← hc]
    have e : (⟨(g : G) * z * (g : G)⁻¹, hgz⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
        g * ⟨z, hs.hzC⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨c', hc'⟩ := isConj_iff.mp hj₀c
  obtain ⟨g', rfl⟩ := quotMk_surjective z₁ c'
  have hgz' : (g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹ ∈
      Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ g'.2 (Subgroup.mul_mem _ hgz hs.hzC))
      (Subgroup.inv_mem _ g'.2)
  have hq2 : quotMk z₁ ⟨(g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹, hgz'⟩ = j₀ := by
    rw [← hc']
    have e : (⟨(g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹, hgz'⟩ :
        ↥(Subgroup.centralizer ({z₁} : Set G))) =
        g' * (⟨(g : G) * z * (g : G)⁻¹, hgz⟩ * ⟨z, hs.hzC⟩) * g'⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hq1]
    rfl
  have ht'E : (g : G) * z * (g : G)⁻¹ ∈ preC z₁ Ek := mem_preC.mpr ⟨hgz, hq1 ▸ htE⟩
  have ht'J : (g : G) * z * (g : G)⁻¹ ∉ J z := by
    intro hJ
    rw [← preC_J_quotW hs] at hJ
    exact htJ (hq1 ▸ (mem_preC.mp hJ).2)
  have ht'2 : orderOf ((g : G) * z * (g : G)⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz2
  have hyJ : (g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹ ∈ J z := by
    rw [← preC_J_quotW hs]
    exact mem_preC.mpr ⟨hgz', hq2 ▸ hj₀J⟩
  have hyZ : (g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹ ∉ centerIn (J z) := by
    intro hy
    exact hj₀w (hq2 ▸ quotMk_mem_zpowers_of_mem_centerIn hs hy hgz')
  have hED : preC z₁ Ek ≤ Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁ :=
    le_inf Subgroup.le_normalizer (preC_mono hEK₁)
  have hDclause : ∀ L : Subgroup G, preC z₁ Ek ≤ L →
      L ≤ Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁ →
      L.relIndex (Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁) ≠ 2 := by
    refine (CFSG.GroupTheory.forall_relIndex_ne_two_iff_quotient (E := preC z₁ Ek)
      (K := Subgroup.normalizer (preC z₁ Ek : Set G) ⊓ preC z₁ K₁) hED (hN := hND)).mpr ?_
    intro T hT
    let mk : ↥Kp →* (↥Kp ⧸ Ek.subgroupOf Kp) :=
      QuotientGroup.mk' (Ek.subgroupOf Kp) (nN := hKpN)
    have hmks : Function.Surjective mk :=
      QuotientGroup.mk'_surjective (Ek.subgroupOf Kp) (nN := hKpN)
    let T' : Subgroup (↥Kp ⧸ Ek.subgroupOf Kp) := T.map eD.toMonoidHom
    have hT' : T'.index = 2 := (Subgroup.index_map_equiv (H := T) eD).trans hT
    let L' : Subgroup (QuotC z₁) := (T'.comap mk).map Kp.subtype
    have hEkL' : Ek ≤ L' := by
      intro x hx
      refine ⟨⟨x, hEKp hx⟩, ?_, rfl⟩
      have h1 : mk ⟨x, hEKp hx⟩ = 1 := by
        change (QuotientGroup.mk' (Ek.subgroupOf Kp)) ⟨x, hEKp hx⟩ = 1
        rw [QuotientGroup.mk'_apply (Ek.subgroupOf Kp) (nN := hKpN),
          QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hx
      change mk ⟨x, hEKp hx⟩ ∈ T'
      rw [h1]
      exact T'.one_mem
    have hL'rel : L'.relIndex Kp = 2 := by
      change (L'.subgroupOf Kp).index = 2
      rw [show L'.subgroupOf Kp = T'.comap mk from
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective Kp) _,
        Subgroup.index_comap_of_surjective _ hmks]
      exact hT'
    exact hKpQ L' hEkL' (Subgroup.map_subtype_le _) hL'rel
  refine ⟨preC z₁ K₁, preC_le_centralizer _, ?_, J_le_preC_of_index_two hs hJ' hK₁i,
    ⟨hN₁, X₁, _, hX₁, ⟨eU.trans e₁⟩⟩, preC z₁ Ek, hE, preC_mono hEK₁,
    ⟨hND, (Nat.card_congr eD.toEquiv).trans hKpcard, hDclause⟩,
    (g : G) * z * (g : G)⁻¹,
    (g' : G) * (((g : G) * z * (g : G)⁻¹) * z) * (g' : G)⁻¹, ht'E, ht'J, ht'2,
    isConj_iff.mpr ⟨g, rfl⟩, hyJ, hyZ, isConj_iff.mpr ⟨g', rfl⟩⟩
  rw [relIndex_preC_centralizer, hK₁i]


end CFSG.RankThree.GF2n.Parrott
