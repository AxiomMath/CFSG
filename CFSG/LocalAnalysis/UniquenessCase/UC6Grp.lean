module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {u : G} (hu : u ∈ H ⊔ K) :
    ∃ x ∈ H, ∃ y ∈ K, u = x * y := by
  have hcomm : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hrange := MonoidHom.noncommCoprod_range H.subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  have hu' : u ∈ (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range := by
    rw [hrange]; exact hu
  obtain ⟨⟨a, b⟩, hab⟩ := hu'
  exact ⟨a, a.2, b, b.2, by simpa using hab.symm⟩

theorem card_sup_of_commute_of_disjoint {H K : Subgroup G}
    (hc : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hcomm : ∀ (a : ↥H) (b : ↥K), Commute (H.subtype a) (K.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod H.subtype K.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective H.subtype K.subtype hcomm).2 ?_
    refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range = H ⊔ K := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(H ⊔ K) = Nat.card (MonoidHom.noncommCoprod H.subtype K.subtype hcomm).range := by
        rw [hrange]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod _ _

theorem centralizer_singleton_ne_top (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {x : G} (hx : x ≠ 1) : centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({x} : Set G) := by rw [h]; exact mem_top g
    rw [mem_centralizer_iff] at hg
    exact (hg x rfl).symm
  rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · exact hx (by simpa [hb] using hxc)
  · obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center G := by rw [ht]; exact mem_top a
    exact hab (Subgroup.mem_center_iff.1 this b).symm

theorem le_normalizer_pCoreOf (p : ℕ) (M : Subgroup G) :
    M ≤ normalizer (pCoreOf p M : Set G) := by
  have hle : pCoreOf p M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le p M
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  have hN : (pCoreOf p M).subgroupOf M = pCore p M := by
    ext y
    simp [pCoreOf, Subgroup.mem_subgroupOf]
  rw [hN]
  exact CFSG.LieType.BorelTits.pCore_normal p

theorem pCoreOf_ne_bot_of_isTwoLocal {M : Subgroup G} (hM : IsTwoLocal M) : pCoreOf 2 M ≠ ⊥ := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hM
  intro h
  have hP : P ≤ pCoreOf 2 (normalizer (P : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
  rw [h] at hP
  exact hP1 (le_bot_iff.1 hP)

end CFSG.LocalAnalysis.UniquenessCase.UC6
