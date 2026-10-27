module

public import CFSG.Sporadic.Recognition.LyonsLocalNormalizerA3
public import CFSG.Sporadic.Recognition.LyonsLocalEdge

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

variable {G : Type*} [Group G]

abbrev inNormX {X₁ : G} (X₂ : G) (h : X₂ ∈ NormX X₁) : ↥(NormX X₁) := ⟨X₂, h⟩

theorem subgroupOf_zpowers_of_mem {B : Subgroup G} {g : G} (hg : g ∈ B) :
    (zpowers g).subgroupOf B = zpowers (⟨g, hg⟩ : B) := by
  ext b
  rw [mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

theorem subgroupOf_closure_triple_of_mem {B : Subgroup G} {a b c : G} (ha : a ∈ B) (hb : b ∈ B)
    (hc : c ∈ B) :
    (closure ({a, b, c} : Set G)).subgroupOf B =
      closure ({⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} : Set B) := by
  have hle : closure ({a, b, c} : Set G) ≤ B := by
    rw [closure_le]
    rintro t (rfl | rfl | rfl) <;> assumption
  apply map_injective B.subtype_injective
  rw [map_subgroupOf_eq_of_le hle, MonoidHom.map_closure]
  simp [Set.image_insert_eq]

theorem subgroupOf_inf_eq_inf (H K B : Subgroup G) :
    (H ⊓ K).subgroupOf B = H.subgroupOf B ⊓ K.subgroupOf B :=
  comap_inf H K B.subtype

theorem closure_triple_eq_of_eq_or_inv {Γ : Type*} [Group Γ] {x y w y' w' : Γ}
    (hy : y' = y ∨ y' = y⁻¹) (hw : w' = w ∨ w' = w⁻¹) :
    closure ({x, y', w'} : Set Γ) = closure ({x, y, w} : Set Γ) := by
  have key : ∀ {y w y' w' : Γ}, (y' = y ∨ y' = y⁻¹) → (w' = w ∨ w' = w⁻¹) →
      closure ({x, y', w'} : Set Γ) ≤ closure ({x, y, w} : Set Γ) := by
    intro y w y' w' hy hw
    have hx : x ∈ closure ({x, y, w} : Set Γ) := subset_closure (by simp)
    have hy₀ : y ∈ closure ({x, y, w} : Set Γ) := subset_closure (by simp)
    have hw₀ : w ∈ closure ({x, y, w} : Set Γ) := subset_closure (by simp)
    have hy' : y' ∈ closure ({x, y, w} : Set Γ) := by
      rcases hy with rfl | rfl
      · exact hy₀
      · exact inv_mem hy₀
    have hw' : w' ∈ closure ({x, y, w} : Set Γ) := by
      rcases hw with rfl | rfl
      · exact hw₀
      · exact inv_mem hw₀
    rw [closure_le]
    rintro t (rfl | rfl | rfl)
    exacts [hx, hy', hw']
  refine le_antisymm (key hy hw) (key ?_ ?_)
  · rcases hy with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, inv_inv])
  · rcases hw with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, inv_inv])

theorem map_subgroupOf_normalizer_eq {B H : Subgroup G} (hH : H ≤ B) {Γ : Type*} [Group Γ]
    (φ : B ≃* Γ) :
    ((normalizer (H : Set G)).subgroupOf B).map φ.toMonoidHom =
      normalizer (((H.subgroupOf B).map φ.toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [subgroupOf_normalizer_eq hH, map_equiv_normalizer_eq]

theorem map_subgroupOf_normalizer_zpowers {B : Subgroup G} {g : G} (hg : g ∈ B) {Γ : Type*}
    [Group Γ] (φ : B ≃* Γ) :
    ((normalizer (zpowers g : Set G)).subgroupOf B).map φ.toMonoidHom =
      normalizer (zpowers (φ ⟨g, hg⟩) : Set Γ) := by
  rw [map_subgroupOf_normalizer_eq (zpowers_le.2 hg), subgroupOf_zpowers_of_mem hg,
    MonoidHom.map_zpowers]
  rfl

theorem map_subgroupOf_closure_triple {B : Subgroup G} {a b c : G} (ha : a ∈ B) (hb : b ∈ B)
    (hc : c ∈ B) {Γ : Type*} [Group Γ] (φ : B ≃* Γ) :
    ((closure ({a, b, c} : Set G)).subgroupOf B).map φ.toMonoidHom =
      closure ({φ ⟨a, ha⟩, φ ⟨b, hb⟩, φ ⟨c, hc⟩} : Set Γ) := by
  rw [subgroupOf_closure_triple_of_mem ha hb hc, MonoidHom.map_closure]
  simp [Set.image_insert_eq]

theorem map_normalizers_of_mulEquiv {X₁ X₂ X₃ : G} (h₁ : X₁ ∈ NormX X₁) (h₂ : X₂ ∈ NormX X₁)
    (h₃ : X₃ ∈ NormX X₁) {Γ : Type*} [Group Γ] (φ : ↥(NormX X₁) ≃* Γ) {x y w : Γ}
    (hx : φ ⟨X₁, h₁⟩ = x) (hy : φ ⟨X₂, h₂⟩ = y ∨ φ ⟨X₂, h₂⟩ = y⁻¹)
    (hw : φ ⟨X₃, h₃⟩ = w ∨ φ ⟨X₃, h₃⟩ = w⁻¹) :
    ((NN X₁ X₂).subgroupOf (NormX X₁)).map φ.toMonoidHom = normalizer (zpowers y : Set Γ) ∧
    ((normalizer (A3 X₁ X₂ X₃ : Set G)).subgroupOf (NormX X₁)).map φ.toMonoidHom =
      normalizer ((closure ({x, y, w} : Set Γ) : Subgroup Γ) : Set Γ) ∧
    ((NN X₁ X₂ ⊓ normalizer (zpowers X₃ : Set G)).subgroupOf (NormX X₁)).map φ.toMonoidHom =
      normalizer (zpowers x : Set Γ) ⊓ normalizer (zpowers y : Set Γ) ⊓
        normalizer (zpowers w : Set Γ) := by
  have hzy : zpowers (φ ⟨X₂, h₂⟩) = zpowers y := by
    rcases hy with h | h
    · rw [h]
    · rw [h, zpowers_inv]
  have hzw : zpowers (φ ⟨X₃, h₃⟩) = zpowers w := by
    rcases hw with h | h
    · rw [h]
    · rw [h, zpowers_inv]
  have e₁ := map_subgroupOf_normalizer_zpowers h₁ φ
  have e₂ := map_subgroupOf_normalizer_zpowers h₂ φ
  have e₃ := map_subgroupOf_normalizer_zpowers h₃ φ
  rw [hx] at e₁
  rw [hzy] at e₂
  rw [hzw] at e₃
  refine ⟨?_, ?_, ?_⟩
  · rw [NN, inf_subgroupOf_left]
    exact e₂
  · have hle : A3 X₁ X₂ X₃ ≤ NormX X₁ := by
      rw [A3, closure_le]
      rintro t (rfl | rfl | rfl) <;> assumption
    have e : ((A3 X₁ X₂ X₃).subgroupOf (NormX X₁)).map φ.toMonoidHom =
        closure ({x, y, w} : Set Γ) := by
      rw [A3, map_subgroupOf_closure_triple h₁ h₂ h₃ φ, hx]
      exact closure_triple_eq_of_eq_or_inv hy hw
    rw [map_subgroupOf_normalizer_eq hle φ, e]
  · rw [NN, subgroupOf_inf_eq_inf, subgroupOf_inf_eq_inf, map_inf_eq _ _ _ φ.injective,
      map_inf_eq _ _ _ φ.injective, e₁, e₂, e₃]

end CFSG.Sporadic.Recognition.LyonsSims
