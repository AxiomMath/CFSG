module

public import CFSG.OddTranspositions.BlockTransitive

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {D : Set G}

@[expose] def blockUnion (V : Set (Set G)) : Set G := {x | ∃ β ∈ V, x ∈ β}

theorem blockUnion_conj (V : Set (Set G)) (g : G) :
    (fun x => g * x * g⁻¹) '' blockUnion V =
      blockUnion ((fun β => (fun x => g * x * g⁻¹) '' β) '' V) := by
  ext x
  constructor
  · rintro ⟨y, ⟨β, hβ, hy⟩, rfl⟩
    exact ⟨_, ⟨β, hβ, rfl⟩, y, hy, rfl⟩
  · rintro ⟨β, ⟨γ, hγ, rfl⟩, y, hy, rfl⟩
    exact ⟨y, ⟨γ, hγ, hy⟩, rfl⟩

theorem blockUnion_subset {D α : Set G} {V : Set (Set G)} (hN : IsNormalSet D) (hα : IsBlock D α)
    (hV : V ⊆ blockClass α) : blockUnion V ⊆ D := by
  rintro x ⟨β, hβ, hx⟩
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp (hV hβ)
  obtain ⟨y, hy, rfl⟩ := hx
  exact hN g y (hα.subset hy)

theorem blockUnion_nonempty {D α : Set G} {V : Set (Set G)} (hα : IsBlock D α) (hV : V ⊆ blockClass α)
    (hne : V.Nonempty) : (blockUnion V).Nonempty := by
  obtain ⟨β, hβ⟩ := hne
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp (hV hβ)
  obtain ⟨x, hx⟩ := hα.nonempty
  exact ⟨g * x * g⁻¹, (fun y => g * y * g⁻¹) '' α, hβ, ⟨x, hx, rfl⟩⟩

theorem isBlock_blockUnion {D α : Set G} {V : Set (Set G)} (hN : IsNormalSet D) (hα : IsBlock D α)
    (hV : V ⊆ blockClass α) (hVb : MulAction.IsBlock (ConjAct G) V)
    (hne : V.Nonempty) (hproper : V ≠ blockClass α) :
    IsBlock D (blockUnion V) := by
  classical
  refine ⟨blockUnion_subset hN hα hV, blockUnion_nonempty hα hV hne, ?_, ?_⟩
  · intro hU
    obtain ⟨γ, hγc, hγV⟩ : ∃ γ ∈ blockClass α, γ ∉ V := by
      by_contra h
      push Not at h
      exact hproper (Set.Subset.antisymm hV h)
    obtain ⟨h, rfl⟩ := mem_blockClass_iff.mp hγc
    obtain ⟨x, hxγ⟩ := hα.nonempty
    have hxγ' : h * x * h⁻¹ ∈ (fun y => h * y * h⁻¹) '' α := ⟨x, hxγ, rfl⟩
    have hxD : h * x * h⁻¹ ∈ D := hN h x (hα.subset hxγ)
    have hxU : h * x * h⁻¹ ∈ blockUnion V := hU ▸ hxD
    obtain ⟨β, hβV, hxβ⟩ := hxU
    have hβc : β ∈ blockClass α := hV hβV
    have hβγ : β = (fun y => h * y * h⁻¹) '' α :=
      eq_of_mem_of_mem_blockClass hα hβc hγc ⟨_, hxβ, hxγ'⟩
    exact hγV (hβγ ▸ hβV)
  · intro g hg
    by_contra hdis
    rw [Set.not_disjoint_iff] at hdis
    obtain ⟨x, hxU, hxgU⟩ := hdis
    rw [blockUnion_conj] at hxgU
    obtain ⟨β, hβV, hxβ⟩ := hxU
    obtain ⟨γ, ⟨δ, hδV, rfl⟩, hxγ⟩ := hxgU
    have hβc : β ∈ blockClass α := hV hβV
    have hγc : (fun y => g * y * g⁻¹) '' δ ∈ blockClass α := by
      obtain ⟨h, rfl⟩ := mem_blockClass_iff.mp (hV hδV)
      exact mem_blockClass_iff.mpr ⟨g * h, by
        simp only [Set.image_image]
        congr 1
        ext z
        group⟩
    have hβγ : β = (fun y => g * y * g⁻¹) '' δ :=
      eq_of_mem_of_mem_blockClass hα hβc hγc ⟨_, hxβ, hxγ⟩
    have hβV' : β ∈ (fun β => (fun x => g * x * g⁻¹) '' β) '' V :=
      ⟨δ, hδV, hβγ.symm⟩
    have hsmulV : ConjAct.toConjAct g • V =
        (fun β => (fun x => g * x * g⁻¹) '' β) '' V := by
      have hfun : (fun β : Set G => ConjAct.toConjAct g • β) =
          (fun β => (fun x => g * x * g⁻¹) '' β) := by
        funext β
        rw [← Set.image_smul]
        rfl
      rw [← Set.image_smul, hfun]
    have hinter : (ConjAct.toConjAct g • V ∩ V).Nonempty := by
      rw [hsmulV]
      exact ⟨β, hβV', hβV⟩
    have hfix : ConjAct.toConjAct g • V = V := by
      simpa using (MulAction.isBlock_iff_smul_eq_smul_of_nonempty.mp hVb)
        (g₁ := ConjAct.toConjAct g) (g₂ := 1) (by simpa using hinter)
    have hUfix : (fun x => g * x * g⁻¹) '' blockUnion V = blockUnion V := by
      rw [blockUnion_conj, ← hsmulV, hfix]
    exact hg (Subgroup.mem_normalizer_iff_conj_image_eq.mpr hUfix)

theorem Valpha_eq_singleton_of_isMaxBlock_of_ne {D α : Set G} (hN : IsNormalSet D)
    (hmax : IsMaxBlock D α) (hproper : Valpha D α ≠ blockClass α) :
    Valpha D α = {α} := by
  classical
  have hα : IsBlock D α := IsMaxBlock.isBlock hmax
  have hV : Valpha D α ⊆ blockClass α := fun _ h => h.1
  have hVb : MulAction.IsBlock (ConjAct G) (Valpha D α) := isBlockSet_Valpha hN
  have hne : (Valpha D α).Nonempty := ⟨α, mem_Valpha_self D α⟩
  have hUblock : IsBlock D (blockUnion (Valpha D α)) :=
    isBlock_blockUnion hN hα hV hVb hne hproper
  have hαU : α ⊆ blockUnion (Valpha D α) := fun x hx => ⟨α, mem_Valpha_self D α, hx⟩
  have hUeq : blockUnion (Valpha D α) = α :=
    hmax.2.2.2.2 (blockUnion (Valpha D α)) hαU (IsBlock.subset hUblock) (IsBlock.ne_univ hUblock) (IsBlock.isBlock hUblock)
  ext β
  constructor
  · intro hβ
    have hβc : β ∈ blockClass α := hV hβ
    have hβne : β.Nonempty := by
      obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβc
      obtain ⟨x, hx⟩ := hα.nonempty
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩⟩
    have hβα : β ⊆ α := by
      intro x hx
      rw [← hUeq]
      exact ⟨β, hβ, hx⟩
    have hβeq : β = α :=
      eq_of_mem_of_mem_blockClass hα hβc (mem_blockClass_self α) ⟨_, hβne.choose_spec, hβα hβne.choose_spec⟩
    rw [Set.mem_singleton_iff]
    exact hβeq
  · intro hβ
    rw [Set.mem_singleton_iff] at hβ
    rw [hβ]
    exact mem_Valpha_self D α

theorem Walpha_eq_singleton_of_isMaxBlock_of_ne {D α : Set G} (hN : IsNormalSet D)
    (hmax : IsMaxBlock D α) (hproper : Walpha D α ≠ blockClass α) :
    Walpha D α = {α} := by
  classical
  have hα : IsBlock D α := IsMaxBlock.isBlock hmax
  have hV : Walpha D α ⊆ blockClass α := fun _ h => h.1
  have hVb : MulAction.IsBlock (ConjAct G) (Walpha D α) := isBlockSet_Walpha hN
  have hne : (Walpha D α).Nonempty := ⟨α, mem_Walpha_self D α⟩
  have hUblock : IsBlock D (blockUnion (Walpha D α)) :=
    isBlock_blockUnion hN hα hV hVb hne hproper
  have hαU : α ⊆ blockUnion (Walpha D α) := fun x hx => ⟨α, mem_Walpha_self D α, hx⟩
  have hUeq : blockUnion (Walpha D α) = α :=
    hmax.2.2.2.2 (blockUnion (Walpha D α)) hαU (IsBlock.subset hUblock) (IsBlock.ne_univ hUblock) (IsBlock.isBlock hUblock)
  ext β
  constructor
  · intro hβ
    have hβc : β ∈ blockClass α := hV hβ
    have hβne : β.Nonempty := by
      obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hβc
      obtain ⟨x, hx⟩ := hα.nonempty
      exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩⟩
    have hβα : β ⊆ α := by
      intro x hx
      rw [← hUeq]
      exact ⟨β, hβ, hx⟩
    have hβeq : β = α :=
      eq_of_mem_of_mem_blockClass hα hβc (mem_blockClass_self α) ⟨_, hβne.choose_spec, hβα hβne.choose_spec⟩
    rw [Set.mem_singleton_iff]
    exact hβeq
  · intro hβ
    rw [Set.mem_singleton_iff] at hβ
    rw [hβ]
    exact mem_Walpha_self D α

end CFSG.OddTranspositions
