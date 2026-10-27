module

public import CFSG.Quasithin.EmptyFaithful.S153NBa2
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.S153N

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Card

theorem card_map_eq_relIndex {G Q : Type} [Group G] [Group Q] {C A K : Subgroup G} (hAC : A ≤ C)
    (φ : ↥C →* Q) (hker : φ.ker = K.subgroupOf C) :
    Nat.card ↥((A.subgroupOf C).map φ) = (A ⊓ K).relIndex A := by
  set H : Subgroup ↥C := A.subgroupOf C with hH
  have h1 : (φ.comp H.subtype).range = H.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h2 := Subgroup.index_ker (φ.comp H.subtype)
  rw [h1] at h2
  rw [← h2]
  have h3 : (φ.comp H.subtype).ker = (K.subgroupOf C).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show φ (x : ↥C) = 1 ↔ (((x : ↥C) : G)) ∈ K
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [h3]
  have h4 : ((K.subgroupOf C).subgroupOf H).index = (K.subgroupOf C).relIndex H := rfl
  rw [h4, hH, Subgroup.relIndex_subgroupOf hAC]
  unfold Subgroup.relIndex
  rw [Subgroup.inf_subgroupOf_left]

end Card

section Fix

variable {U : Type} [CommGroup U] {Cg : Type} [Group Cg]

theorem map_fixV_eq_fixSet (σ : MulAut U) (ρ : Cg →* MulAut U)
    (hρσ : ∀ (c : Cg) (u : U), ρ c (σ u) = σ (ρ c u)) (H : Subgroup Cg) :
    (fixV (H.map (phiHom σ ρ hρσ))).map (S1567.fixSub σ).subtype =
      S1567.fixSub σ ⊓ S1567.fixSet ((H.map ρ : Subgroup (MulAut U)) : Set (MulAut U)) := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, ?_⟩
    rintro g ⟨x, hx, rfl⟩
    have := hw (phiHom σ ρ hρσ x) ⟨x, hx, rfl⟩
    exact congrArg Subtype.val this
  · rintro ⟨hu, hS⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    exact hS (ρ x) ⟨x, hx, rfl⟩

end Fix

end CFSG.Quasithin.S153N
