module

public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def ActsTriviallyOnBlocks (α : Set G) (x : G) : Prop :=
  ∀ β ∈ blockClass α, (fun y => x * y * x⁻¹) '' β = β

@[expose] def FaithfulOnBlocks (α : Set G) : Prop :=
  ∀ x : G, ActsTriviallyOnBlocks α x → x = 1

theorem perp_union_Aalpha_eq_blockClass (D α : Set G) :
    perp D α ∪ Aalpha D α = blockClass α := by
  ext β
  rw [Set.mem_union β (perp D α) (Aalpha D α), mem_Aalpha_iff]
  constructor
  · rintro (h | ⟨h, -⟩)
    · rw [mem_perp_iff] at h
      rcases h with h | rfl
      · exact h.1
      · exact mem_blockClass_self _
    · exact h
  · intro hβ
    by_cases h : β ∈ perp D α
    · exact Or.inl h
    · exact Or.inr ⟨hβ, h⟩

theorem ActsTriviallyOnBlocks.conj {α : Set G} {x : G} (hx : ActsTriviallyOnBlocks α x) (g : G) :
    ActsTriviallyOnBlocks α (g * x * g⁻¹) := by
  intro β hβ
  have hβ' : (fun z => g⁻¹ * z * g) '' β ∈ blockClass α := by
    rw [mem_blockClass_iff] at hβ ⊢
    obtain ⟨k, rfl⟩ := hβ
    refine ⟨g⁻¹ * k, ?_⟩
    simp only [Set.image_image]
    congr 1
    funext z
    group
  have h1 : (fun z => x * z * x⁻¹) '' ((fun z => g⁻¹ * z * g) '' β) =
      (fun z => g⁻¹ * z * g) '' β := hx _ hβ'
  calc (fun z => (g * x * g⁻¹) * z * (g * x * g⁻¹)⁻¹) '' β
      = (fun z => g * (x * (g⁻¹ * z * g) * x⁻¹) * g⁻¹) '' β := by
        congr 1
        funext z
        group
    _ = (fun z => g * z * g⁻¹) ''
          ((fun w => x * w * x⁻¹) '' ((fun z => g⁻¹ * z * g) '' β)) := by
        rw [Set.image_image, Set.image_image]
    _ = (fun z => g * z * g⁻¹) '' ((fun z => g⁻¹ * z * g) '' β) := by rw [h1]
    _ = β := by
        rw [Set.image_image]
        have h : (fun z => g * (g⁻¹ * z * g) * g⁻¹) = id := by
          funext z
          show g * (g⁻¹ * z * g) * g⁻¹ = z
          group
        rw [h, Set.image_id]

def blockKernel (α : Set G) : Subgroup G where
  carrier := {x | ActsTriviallyOnBlocks α x}
  one_mem' := by
    intro β _
    simp
  mul_mem' := by
    intro x y hx hy β hβ
    calc (fun z => (x * y) * z * (x * y)⁻¹) '' β
        = (fun z => x * (y * z * y⁻¹) * x⁻¹) '' β := by
          congr 1
          funext z
          group
      _ = (fun z => x * z * x⁻¹) '' ((fun z => y * z * y⁻¹) '' β) := by
          rw [Set.image_image]
      _ = β := by rw [hy β hβ, hx β hβ]
  inv_mem' := by
    intro x hx β hβ
    simp only [inv_inv]
    have himg : (fun z => x * z * x⁻¹) '' β = β := hx β hβ
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      show x⁻¹ * z * x ∈ β
      have hxz : x * (x⁻¹ * z * x) * x⁻¹ ∈ β := by
        rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group]
      rw [← himg] at hxz
      obtain ⟨u, hu, huz⟩ := hxz
      have huz' : u = x⁻¹ * z * x := by
        have h := congrArg (fun w => x⁻¹ * w * x) huz
        rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group,
          show x⁻¹ * (x * (x⁻¹ * z * x) * x⁻¹) * x = x⁻¹ * z * x by group] at h
        exact h
      rwa [← huz']
    · intro hw
      refine ⟨x * w * x⁻¹, ?_, ?_⟩
      · rw [← himg]
        exact ⟨w, hw, rfl⟩
      · show x⁻¹ * (x * w * x⁻¹) * x = w
        group

theorem mem_blockKernel_iff {α : Set G} {x : G} :
    x ∈ blockKernel α ↔ ActsTriviallyOnBlocks α x := by
  rfl

theorem blockKernel_normal (α : Set G) : (blockKernel α).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_blockKernel_iff] at hx ⊢
  exact hx.conj g

theorem faithfulOnBlocks_iff_blockKernel_eq_bot {α : Set G} :
    FaithfulOnBlocks α ↔ blockKernel α = ⊥ := by
  constructor
  · intro hF
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hF x (by rwa [mem_blockKernel_iff] at hx)
  · intro hbot x hx
    have hx' : x ∈ blockKernel α := by
      rw [mem_blockKernel_iff]
      exact hx
    rw [hbot] at hx'
    simpa using hx'

end CFSG.OddTranspositions
