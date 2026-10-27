module

public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def C118Univ (B C₁ C₂ : Subgroup G) : Prop :=
  ∀ (Ω : Type) [Group Ω] [Finite Ω] (H : Subgroup Ω) (ι : ↥B →* Ω),
    Function.Injective ι → InClassG H ι.range →
      (C₁.subgroupOf B).map ι ≤ centerOf H ∨
      H ≤ Subgroup.normalizer (((C₂.subgroupOf B).map ι : Subgroup Ω) : Set Ω) ∨
      IsL2OrA3Block H (twoResidual H)

@[expose] def IsC118WeakPair (S C₁ C₂ : Subgroup G) : Prop :=
  C₁ ≠ ⊥ ∧ C₁ ≤ omegaOneCenterOf S ∧ C₂ ≠ ⊥ ∧ C₂ ≤ baum S ∧
    (C₂.subgroupOf (baum S)).Characteristic ∧ C118Univ (baum S) C₁ C₂

theorem IsC118Pair.toWeakSelf {S C₁ C₂ : Subgroup G} (h : IsC118Pair S C₁ C₂) :
    IsC118WeakPair S C₁ C₂ := by
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h4, h5, h6, h7⟩

theorem omegaOneCenterOf_le_omegaOneCenterOf_of_baum_le {S T : Subgroup G} (hbS : baum T ≤ S)
    (hST : S ≤ T) : omegaOneCenterOf T ≤ omegaOneCenterOf S := by
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  have hxZ : x ∈ omegaOneCenterOf T := Subgroup.subset_closure hx
  have hxS : x ∈ S := hbS (C1GN.omegaOneCenterOf_le_baum T hxZ)
  have hxc : x ∈ T ⊓ Subgroup.centralizer (T : Set G) := hx.1
  refine Subgroup.subset_closure ⟨⟨hxS, Subgroup.mem_centralizer_iff.2 ?_⟩, hx.2⟩
  intro y hy
  exact Subgroup.mem_centralizer_iff.1 hxc.2 y (hST hy)

theorem IsC118Pair.toWeakOfBaumEq {S T C₁ C₂ : Subgroup G} (h : IsC118Pair T C₁ C₂)
    (hB : baum S = baum T) (h1S : C₁ ≤ omegaOneCenterOf S) : IsC118WeakPair S C₁ C₂ := by
  obtain ⟨h1, -, -, h4, h5, h6, h7⟩ := h
  rw [← hB] at h5 h6 h7
  exact ⟨h1, h1S, h4, h5, h6, h7⟩

theorem IsC118Pair.toWeakOfLe [Finite G] {S T C₁ C₂ : Subgroup G} (h : IsC118Pair T C₁ C₂)
    (hbS : baum T ≤ S) (hST : S ≤ T) : IsC118WeakPair S C₁ C₂ :=
  h.toWeakOfBaumEq (baum_eq_of_le hbS hST).symm
    (h.2.1.trans (omegaOneCenterOf_le_omegaOneCenterOf_of_baum_le hbS hST))

theorem IsC118Pair.toWeak [Finite G] {S T C₁ C₂ : Subgroup G} (h : IsC118Pair T C₁ C₂)
    (_hT : IsPGroup 2 T) (hbS : baum T ≤ S) (hST : S ≤ T) : IsC118WeakPair S C₁ C₂ :=
  h.toWeakOfLe hbS hST

theorem IsC118WeakPair.dichotomy {G : Type} [Group G] [Finite G] {C₁ C₂ S H : Subgroup G}
    (hP : IsC118WeakPair S C₁ C₂) (hH : InClassG H (baum S)) :
    C₁ ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ : Set G) ∨
      IsL2OrA3Block H (twoResidual H) := by
  obtain ⟨-, h1Z, -, h2B, -, hall⟩ := hP
  have h1B : C₁ ≤ baum S := h1Z.trans (C1GN.omegaOneCenterOf_le_baum S)
  have := hall G H (baum S).subtype (baum S).subtype_injective (by rwa [Subgroup.range_subtype])
  rwa [Subgroup.map_subgroupOf_eq_of_le h1B, Subgroup.map_subgroupOf_eq_of_le h2B] at this

end CFSG.Quasithin
