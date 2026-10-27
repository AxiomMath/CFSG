module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open Subgroup

theorem owEm_card_closure_conj {G : Type*} [Group G] (m : G) (S : Set G) :
    Nat.card (closure ((fun x => m * x * m⁻¹) '' S)) = Nat.card (closure S) := by
  have h : closure ((fun x => m * x * m⁻¹) '' S) = (closure S).map (MulAut.conj m).toMonoidHom := by
    rw [MonoidHom.map_closure]
    rfl
  rw [h]
  exact Nat.card_congr ((closure S).equivMapOfInjective (MulAut.conj m).toMonoidHom
    (MulAut.conj m).injective).symm

theorem owEm_commute_conj {G : Type*} [Group G] (c x y : G) :
    Commute (c⁻¹ * x * c) y ↔ Commute x (c * y * c⁻¹) := by
  unfold Commute SemiconjBy
  constructor
  · intro h
    calc x * (c * y * c⁻¹) = c * (c⁻¹ * x * c * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * x := by group
  · intro h
    calc c⁻¹ * x * c * y = c⁻¹ * (x * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * x) * c := by rw [h]
      _ = y * (c⁻¹ * x * c) := by group

theorem owEm_l51_of_class_data {G : Type*} [Group G] (M : Subgroup G) (P : G → Prop)
    (hPconj : ∀ g m : G, m ∈ M → P g → P (m * g * m⁻¹))
    (X : Set G) (r₀ : G) (hr₀ : r₀ ∈ M) (hX₀ : r₀ ∈ X)
    (hXconj : ∀ x ∈ X, ∃ m ∈ M, x = m * r₀ * m⁻¹)
    (hXclosed : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hone : ∀ g ∈ M, P g → ∃ m ∈ M, r₀ = m * g * m⁻¹)
    (hwit : ∀ x ∈ X, orderOf (r₀ * x) = 3 → ∃ t ∈ X, ¬ (Commute t r₀ ∧ Commute t x) ∧
      ¬ Nat.card (closure ({r₀, x, t} : Set G)) ∣ 48) :
    ∀ g₁ ∈ M, ∀ g₂ ∈ M, P g₁ → P g₂ → orderOf (g₁ * g₂) = 3 → ∃ m ∈ M,
      ¬ (Commute (m * g₁ * m⁻¹) g₁ ∧ Commute (m * g₁ * m⁻¹) g₂) ∧
      ¬ Nat.card (closure ({g₁, g₂, m * g₁ * m⁻¹} : Set G)) ∣ 48 := by
  intro g₁ hg₁ g₂ hg₂ hP₁ hP₂ hord
  obtain ⟨m₁, hm₁, hr⟩ := hone g₁ hg₁ hP₁
  have hg₂' : m₁ * g₂ * m₁⁻¹ ∈ M := M.mul_mem (M.mul_mem hm₁ hg₂) (M.inv_mem hm₁)
  obtain ⟨m₂, hm₂, hr₂⟩ := hone _ hg₂' (hPconj g₂ m₁ hm₁ hP₂)
  have hg₂X : m₁ * g₂ * m₁⁻¹ ∈ X := by
    have h := hXclosed m₂⁻¹ (M.inv_mem hm₂) r₀ hX₀
    have e : m₂⁻¹ * r₀ * m₂⁻¹⁻¹ = m₁ * g₂ * m₁⁻¹ := by
      rw [hr₂]; group
    rwa [e] at h
  have hord' : orderOf (r₀ * (m₁ * g₂ * m₁⁻¹)) = 3 := by
    have e : r₀ * (m₁ * g₂ * m₁⁻¹) = m₁ * (g₁ * g₂) * m₁⁻¹ := by rw [hr]; group
    rw [e, ← hord]
    exact orderOf_injective (MulAut.conj m₁).toMonoidHom (MulAut.conj m₁).injective _
  obtain ⟨t, htX, hnc, hcard⟩ := hwit _ hg₂X hord'
  obtain ⟨m₃, hm₃, ht⟩ := hXconj t htX
  have hconj : (m₁⁻¹ * m₃ * m₁) * g₁ * (m₁⁻¹ * m₃ * m₁)⁻¹ = m₁⁻¹ * t * m₁ := by
    have h1 : g₁ = m₁⁻¹ * r₀ * m₁ := by rw [hr]; group
    rw [h1, ht]; group
  refine ⟨m₁⁻¹ * m₃ * m₁, M.mul_mem (M.mul_mem (M.inv_mem hm₁) hm₃) hm₁, ?_, ?_⟩
  · rw [hconj, owEm_commute_conj, owEm_commute_conj]
    have e1 : m₁ * g₁ * m₁⁻¹ = r₀ := hr.symm
    rw [e1]
    exact hnc
  · rw [hconj]
    have hset : ({g₁, g₂, m₁⁻¹ * t * m₁} : Set G) =
        (fun x => m₁⁻¹ * x * m₁⁻¹⁻¹) '' ({r₀, m₁ * g₂ * m₁⁻¹, t} : Set G) := by
      simp only [Set.image_insert_eq, Set.image_singleton]
      have h1 : g₁ = m₁⁻¹ * r₀ * m₁⁻¹⁻¹ := by rw [hr]; group
      have h2 : g₂ = m₁⁻¹ * (m₁ * g₂ * m₁⁻¹) * m₁⁻¹⁻¹ := by group
      have h3 : m₁⁻¹ * t * m₁ = m₁⁻¹ * t * m₁⁻¹⁻¹ := by group
      rw [← h1, ← h2, ← h3]
    rw [hset, owEm_card_closure_conj]
    exact hcard

end CFSG.StandardType.ZS

end
