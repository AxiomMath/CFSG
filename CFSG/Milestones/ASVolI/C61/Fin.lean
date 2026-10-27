module

public import CFSG.Milestones.ASVolI.C61.Emb
public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.Ch3xC58NSEmbA7a

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

theorem burnsideC56_fin_top {G : Type} [Group G] (K : Subgroup G) :
    (⊤ : Subgroup ↥K).map K.subtype = K := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem burnsideC56_fin_sub {G : Type} [Group G] {X K : Subgroup G} (h : X ≤ K) :
    (X.subgroupOf K).map K.subtype = X := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h]

section Setup

variable {G G' : Type} [Group G] [Group G'] {H Λ : Subgroup G} {ι : ↥H →* G'} {κ : ↥Λ →* G'}

theorem burnsideC56_fin_agree
    (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    {X : Subgroup G} (hX : X ≤ Λ ⊓ H) : (X.subgroupOf H).map ι = (X.subgroupOf Λ).map κ := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    replace hx : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hΛ : (x : G) ∈ Λ := (hX hx).1
    refine ⟨⟨x, hΛ⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    exact (hag x x.2 hΛ).symm
  · rintro ⟨y, hy, rfl⟩
    replace hy : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have hH : (y : G) ∈ H := (hX hy).2
    refine ⟨⟨y, hH⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    exact hag y hH y.2

theorem burnsideC56_fin_meet (hag : ∀ g (hH : g ∈ H) (hΛ : g ∈ Λ), ι ⟨g, hH⟩ = κ ⟨g, hΛ⟩)
    (hmeet : ∀ h l, ι h = κ l → (h : G) = l) :
    (⊤ : Subgroup ↥Λ).map κ ⊓ (⊤ : Subgroup ↥H).map ι = ((Λ ⊓ H).subgroupOf H).map ι := by
  ext b
  constructor
  · rintro ⟨⟨l, -, rfl⟩, ⟨h, -, hhl⟩⟩
    have e := hmeet h l hhl
    refine ⟨h, ?_, hhl⟩
    show h ∈ (Λ ⊓ H).subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    exact ⟨e ▸ l.2, h.2⟩
  · rintro ⟨h, hh, rfl⟩
    replace hh : (h : G) ∈ Λ ⊓ H := Subgroup.mem_subgroupOf.mp hh
    refine ⟨⟨⟨h, hh.1⟩, trivial, (hag h h.2 hh.1).symm⟩, ⟨h, trivial, rfl⟩⟩

end Setup

end CFSG.ASVolI
