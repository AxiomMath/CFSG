module

public import CFSG.Sporadic.Recognition.LyonsAS4Centr

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Preim

variable {G : Type*} [Group G] (x : G)

@[expose] def projQ : ↥(centralizer ({x} : Set G)) →* CentQuot x := QuotientGroup.mk' _

theorem projQ_apply (m : ↥(centralizer ({x} : Set G))) : projQ x m = QuotientGroup.mk m := rfl

theorem projQ_surjective : Function.Surjective (projQ x) := QuotientGroup.mk'_surjective _

theorem ker_projQ : (projQ x).ker =
    zpowers (⟨x, self_mem_centralizer_singleton x⟩ : ↥(centralizer ({x} : Set G))) :=
  QuotientGroup.ker_mk' _

theorem card_ker_projQ : Nat.card ↥(projQ x).ker = orderOf x := by
  rw [ker_projQ, Nat.card_zpowers, Subgroup.orderOf_mk]

@[expose] def preimQ (K : Subgroup (CentQuot x)) : Subgroup G :=
  (K.comap (projQ x)).map (centralizer ({x} : Set G)).subtype

variable {x}

theorem mem_preimQ {K : Subgroup (CentQuot x)} {g : G} :
    g ∈ preimQ x K ↔ ∃ h : g ∈ centralizer ({x} : Set G), projQ x ⟨g, h⟩ ∈ K := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨h, hK⟩
    exact ⟨⟨g, h⟩, hK, rfl⟩

theorem preimQ_le_centralizer (K : Subgroup (CentQuot x)) :
    preimQ x K ≤ centralizer ({x} : Set G) := by
  intro g hg
  exact (mem_preimQ.1 hg).1

theorem x_mem_preimQ (K : Subgroup (CentQuot x)) : x ∈ preimQ x K := by
  refine mem_preimQ.2 ⟨self_mem_centralizer_singleton x, ?_⟩
  have : projQ x ⟨x, self_mem_centralizer_singleton x⟩ = 1 := by
    rw [projQ_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers _
  rw [this]
  exact one_mem _

theorem preimQ_mono {K K' : Subgroup (CentQuot x)} (h : K ≤ K') : preimQ x K ≤ preimQ x K' := by
  intro g hg
  obtain ⟨hc, hK⟩ := mem_preimQ.1 hg
  exact mem_preimQ.2 ⟨hc, h hK⟩

theorem card_preimQ (K : Subgroup (CentQuot x)) :
    Nat.card ↥(preimQ x K) = orderOf x * Nat.card ↥K := by
  have hker : (projQ x).ker ≤ K.comap (projQ x) := fun m hm => by
    rw [mem_comap, MonoidHom.mem_ker.1 hm]; exact one_mem _
  have h1 := Subgroup.card_ker_mul_card_range ((projQ x).domRestrict (K.comap (projQ x)))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, Subgroup.map_comap_eq,
    (MonoidHom.range_eq_top.2 (projQ_surjective x)), top_inf_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv, card_ker_projQ] at h1
  rw [preimQ, Subgroup.card_map_of_injective (centralizer ({x} : Set G)).subtype_injective, ← h1]

@[expose] def imQ (x : G) (J : Subgroup G) : Subgroup (CentQuot x) :=
  (J.subgroupOf (centralizer ({x} : Set G))).map (projQ x)

theorem le_preimQ_iff {J : Subgroup G} (hJ : J ≤ centralizer ({x} : Set G))
    {K : Subgroup (CentQuot x)} : J ≤ preimQ x K ↔ imQ x J ≤ K := by
  constructor
  · rintro h _ ⟨m, hm, rfl⟩
    have := h hm
    obtain ⟨hc, hK⟩ := mem_preimQ.1 this
    exact hK
  · intro h g hg
    refine mem_preimQ.2 ⟨hJ hg, h ⟨⟨g, hJ hg⟩, hg, rfl⟩⟩

theorem imQ_isPGroup {p : ℕ} {J : Subgroup G} (hle : J ≤ centralizer ({x} : Set G))
    (hJ : IsPGroup p ↥J) : IsPGroup p ↥(imQ x J) :=
  (hJ.of_equiv (subgroupOfEquivOfLe hle).symm).map _

theorem imQ_normalized {J : Subgroup G}
    {K : Subgroup (CentQuot x)} (hn : ∀ g ∈ preimQ x K, ∀ j ∈ J, g * j * g⁻¹ ∈ J) :
    ∀ c ∈ K, ∀ k ∈ imQ x J, c * k * c⁻¹ ∈ imQ x J := by
  intro c hc k hk
  obtain ⟨j, hj, rfl⟩ := hk
  obtain ⟨m, rfl⟩ := projQ_surjective x c
  have hm : (m : G) ∈ preimQ x K := mem_preimQ.2 ⟨m.2, hc⟩
  refine ⟨m * j * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  show ((m * j * m⁻¹ : ↥(centralizer ({x} : Set G))) : G) ∈ J
  have := hn m hm j hj
  simpa using this

end Preim

end CFSG.Sporadic.Recognition.LyonsSims
