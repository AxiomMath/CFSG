module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open

variable {G : Type*} [Group G]

theorem mem_glbConj_iff {M : Subgroup G} {g x : G} : x ∈ GLBConj g M ↔ g * x * g⁻¹ ∈ M := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem not_dvd_card_inf_conj {p : ℕ} {M : Subgroup G} (hM : GLBStronglyEmbedded p M) {g : G}
    (hg : g ∉ M) : ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G) :=
  hM.2.2 g hg

theorem dvd_card_of_isPGroup_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : p ∣ Nat.card X := by
  rcases hX.card_eq_or_dvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hX1
  · exact h

theorem normalizer_le_of_glbStronglyEmbedded [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : GLBStronglyEmbedded p M) {X : Subgroup G} (hXM : X ≤ M) (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) : Subgroup.normalizer (X : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  apply not_dvd_card_inf_conj hM hgM
  have hle : X ≤ M ⊓ GLBConj g M := by
    intro x hx
    refine ⟨hXM hx, mem_glbConj_iff.mpr (hXM ?_)⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  exact (dvd_card_of_isPGroup_ne_bot hX hX1).trans (Subgroup.card_dvd_of_le hle)

theorem glbStronglyEmbedded_subgroupOf_inf [Finite G] {p : ℕ} {M H : Subgroup G}
    (hM : GLBStronglyEmbedded p M) (hHM : ¬ H ≤ M) (hp : p ∣ Nat.card (H ⊓ M : Subgroup G)) :
    GLBStronglyEmbedded p ((H ⊓ M).subgroupOf H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hHM
    intro h hh
    have : (⟨h, hh⟩ : H) ∈ (H ⊓ M).subgroupOf H := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).2
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ M ≤ H)).toEquiv]
  · intro h hh hdvd
    have hhM : (h : G) ∉ M := fun hm => hh (Subgroup.mem_subgroupOf.mpr ⟨h.2, hm⟩)
    apply not_dvd_card_inf_conj hM hhM
    refine hdvd.trans ?_
    let K : Subgroup H := (H ⊓ M).subgroupOf H ⊓ GLBConj h ((H ⊓ M).subgroupOf H)
    have hmap : K.map H.subtype ≤ M ⊓ GLBConj (h : G) M := by
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(Subgroup.mem_subgroupOf.mp hx1).2, mem_glbConj_iff.mpr ?_⟩
      have h2 := (Subgroup.mem_subgroupOf.mp (mem_glbConj_iff.mp hx2)).2
      simpa using h2
    calc Nat.card K = Nat.card (K.map H.subtype) :=
          (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ ∣ Nat.card (M ⊓ GLBConj (h : G) M : Subgroup G) := Subgroup.card_dvd_of_le hmap

end CFSG.RankThree.PartTwo.Sec21
