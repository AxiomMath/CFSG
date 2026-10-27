module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.RankThree.PartOne.K1320


variable {G : Type} [Group G] {L : Subgroup G} {P : Type} [Group P]

@[expose] def pullG (ε : ↥L →* P) (Q : Subgroup P) : Subgroup G := (Q.comap ε).map L.subtype

theorem pullG_le (ε : ↥L →* P) (Q : Subgroup P) : pullG ε Q ≤ L := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem mem_pullG {ε : ↥L →* P} {Q : Subgroup P} {x : G} :
    x ∈ pullG ε Q ↔ ∃ hx : x ∈ L, ε ⟨x, hx⟩ ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hQ⟩
    exact ⟨⟨x, hx⟩, hQ, rfl⟩

theorem subgroupOf_pullG (ε : ↥L →* P) (Q : Subgroup P) :
    (pullG ε Q).subgroupOf L = Q.comap ε := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hQ⟩ := mem_pullG.1 (Subgroup.mem_subgroupOf.1 hx)
    exact hQ
  · intro hx
    exact Subgroup.mem_subgroupOf.2 (mem_pullG.2 ⟨x.2, hx⟩)

theorem map_subgroupOf_pullG {ε : ↥L →* P} (hs : Function.Surjective ε) (Q : Subgroup P) :
    ((pullG ε Q).subgroupOf L).map ε = Q := by
  rw [subgroupOf_pullG]
  exact Subgroup.map_comap_eq_self_of_surjective hs Q

theorem eq_pullG_of_map {ε : ↥L →* P} (hi : Function.Injective ε) {X : Subgroup G} (hX : X ≤ L)
    {Q : Subgroup P} (hmap : (X.subgroupOf L).map ε = Q) : X = pullG ε Q := by
  apply le_antisymm
  · intro x hx
    have h1 : ε ⟨x, hX hx⟩ ∈ (X.subgroupOf L).map ε :=
      Subgroup.mem_map_of_mem ε (Subgroup.mem_subgroupOf.2 hx)
    rw [hmap] at h1
    exact mem_pullG.2 ⟨hX hx, h1⟩
  · intro x hx
    obtain ⟨hxL, hxQ⟩ := mem_pullG.1 hx
    rw [← hmap] at hxQ
    obtain ⟨y, hy, hyx⟩ := hxQ
    have : y = ⟨x, hxL⟩ := hi hyx
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.1 hy

theorem pullG_mono (ε : ↥L →* P) {Q₁ Q₂ : Subgroup P} (h : Q₁ ≤ Q₂) :
    pullG ε Q₁ ≤ pullG ε Q₂ := by
  intro x hx
  obtain ⟨hxL, hQ⟩ := mem_pullG.1 hx
  exact mem_pullG.2 ⟨hxL, h hQ⟩

theorem pullG_le_iff {ε : ↥L →* P} (hs : Function.Surjective ε) {Q₁ Q₂ : Subgroup P} :
    pullG ε Q₁ ≤ pullG ε Q₂ ↔ Q₁ ≤ Q₂ := by
  refine ⟨fun h y hy => ?_, pullG_mono ε⟩
  obtain ⟨x, rfl⟩ := hs y
  have : (x : G) ∈ pullG ε Q₁ := mem_pullG.2 ⟨x.2, hy⟩
  obtain ⟨_, hQ⟩ := mem_pullG.1 (h this)
  exact hQ

theorem pullG_inf (ε : ↥L →* P) (Q₁ Q₂ : Subgroup P) :
    pullG ε (Q₁ ⊓ Q₂) = pullG ε Q₁ ⊓ pullG ε Q₂ := by
  ext x
  simp only [Subgroup.mem_inf, mem_pullG]
  constructor
  · rintro ⟨hx, h1, h2⟩
    exact ⟨⟨hx, h1⟩, ⟨hx, h2⟩⟩
  · rintro ⟨⟨hx, h1⟩, ⟨_, h2⟩⟩
    exact ⟨hx, h1, h2⟩

theorem pullG_sup {ε : ↥L →* P} (hs : Function.Surjective ε) (hi : Function.Injective ε)
    (Q₁ Q₂ : Subgroup P) : pullG ε (Q₁ ⊔ Q₂) = pullG ε Q₁ ⊔ pullG ε Q₂ := by
  have hle : pullG ε Q₁ ⊔ pullG ε Q₂ ≤ L := sup_le (pullG_le ε Q₁) (pullG_le ε Q₂)
  have hmap : ((pullG ε Q₁ ⊔ pullG ε Q₂).subgroupOf L).map ε = Q₁ ⊔ Q₂ := by
    rw [Subgroup.subgroupOf_sup (pullG_le ε Q₁) (pullG_le ε Q₂), Subgroup.map_sup,
      map_subgroupOf_pullG hs, map_subgroupOf_pullG hs]
  exact (eq_pullG_of_map hi hle hmap).symm

theorem pullG_bot {ε : ↥L →* P} (hi : Function.Injective ε) :
    pullG ε (⊥ : Subgroup P) = ⊥ := by
  ext x
  rw [mem_pullG, Subgroup.mem_bot]
  constructor
  · rintro ⟨hx, h⟩
    rw [Subgroup.mem_bot] at h
    have : (⟨x, hx⟩ : ↥L) = 1 := hi (h.trans (map_one ε).symm)
    exact congrArg Subtype.val this
  · rintro rfl
    exact ⟨L.one_mem, map_one ε⟩

theorem pullG_le_centralizer {ε : ↥L →* P} (hi : Function.Injective ε) {Q₁ Q₂ : Subgroup P}
    (h : Q₁ ≤ Subgroup.centralizer (Q₂ : Set P)) :
    pullG ε Q₁ ≤ Subgroup.centralizer (pullG ε Q₂ : Set G) := by
  intro x hx y hy
  obtain ⟨hxL, hx1⟩ := mem_pullG.1 hx
  obtain ⟨hyL, hy2⟩ := mem_pullG.1 hy
  have hc := Subgroup.mem_centralizer_iff.1 (h hx1) _ hy2
  have : (⟨y, hyL⟩ : ↥L) * ⟨x, hxL⟩ = ⟨x, hxL⟩ * ⟨y, hyL⟩ := hi (by rw [map_mul, map_mul]; exact hc)
  exact congrArg Subtype.val this

theorem card_pullG {ε : ↥L →* P} (hs : Function.Surjective ε) (hi : Function.Injective ε)
    (Q : Subgroup P) : Nat.card (pullG ε Q) = Nat.card Q := by
  have h1 : Nat.card (pullG ε Q) = Nat.card ((pullG ε Q).subgroupOf L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pullG_le ε Q)).toEquiv.symm
  rw [h1, ← Subgroup.card_map_of_injective hi, map_subgroupOf_pullG hs]


end CFSG.RankThree.PartOne.K1320
