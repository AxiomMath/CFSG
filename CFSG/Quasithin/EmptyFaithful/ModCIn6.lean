module

public import CFSG.Quasithin.EmptyFaithful.ModCModel6

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M6

set_option maxRecDepth 100000

@[expose] def ip (x u : PermMod 6) : ZMod 2 := ∑ i, Multiplicative.toAdd x i * Multiplicative.toAdd u i

@[expose] def Hy (u x : PermMod 6) : Prop := (∑ i, Multiplicative.toAdd x i = 0) ∧ ip x u = 0

instance (u x : PermMod 6) : Decidable (Hy u x) := by unfold Hy; infer_instance

@[expose] def Gen (u : PermMod 6) : Finset (PermMod 6) :=
  (Finset.univ.filter fun σ : Perm (Fin 6) => sign σ = 1 ∧ permAct 6 σ u = u).biUnion
    fun σ => (V4 a w).image (permAct 6 σ)

@[expose] def tau (u : PermMod 6) : Perm (Fin 6) :=
  if u = a then swap 4 5 else if u = w then swap 2 3 else swap 0 1

@[expose] def E2 (τ τ' π : Perm (Fin 6)) : Prop := π = 1 ∨ π = τ ∨ π = τ' ∨ π = τ * τ' ∨ π = τ' * τ

instance (τ τ' π : Perm (Fin 6)) : Decidable (E2 τ τ' π) := by unfold E2; infer_instance

theorem mem_Gen {u g : PermMod 6} :
    g ∈ Gen u ↔ ∃ σ : Perm (Fin 6), sign σ = 1 ∧ permAct 6 σ u = u ∧ ∃ q ∈ V4 a w, permAct 6 σ q = g := by
  unfold Gen
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ, q, hq, rfl⟩
    exact ⟨σ, hσ.1, hσ.2, q, hq, rfl⟩
  · rintro ⟨σ, h1, h2, q, hq, rfl⟩
    exact ⟨σ, ⟨h1, h2⟩, q, hq, rfl⟩

theorem cent_a : ∀ π : Perm (Fin 6), (∀ x : PermMod 6, Hy a x → permAct 6 π x = x) →
    π = 1 ∨ π = swap 4 5 := by decide +kernel

theorem cent_w : ∀ π : Perm (Fin 6), (∀ x : PermMod 6, Hy w x → permAct 6 π x = x) →
    π = 1 ∨ π = swap 2 3 := by decide +kernel

theorem cent_aw : ∀ π : Perm (Fin 6), (∀ x : PermMod 6, Hy (a * w) x → permAct 6 π x = x) →
    π = 1 ∨ π = swap 0 1 := by decide +kernel

theorem span_a : ∀ x : PermMod 6, Hy a x →
    ∃ g₁ ∈ Gen a, ∃ g₂ ∈ Gen a, ∃ g₃ ∈ Gen a, x = g₁ * g₂ * g₃ := by decide +kernel

theorem span_w : ∀ x : PermMod 6, Hy w x →
    ∃ g₁ ∈ Gen w, ∃ g₂ ∈ Gen w, ∃ g₃ ∈ Gen w, x = g₁ * g₂ * g₃ := by decide +kernel

theorem span_aw : ∀ x : PermMod 6, Hy (a * w) x →
    ∃ g₁ ∈ Gen (a * w), ∃ g₂ ∈ Gen (a * w), ∃ g₃ ∈ Gen (a * w), x = g₁ * g₂ * g₃ := by decide +kernel

theorem sum_a_w : ∀ x : PermMod 6, (∑ i, Multiplicative.toAdd x i = 0) → ∃ h₁ h₂ : PermMod 6,
    Hy a h₁ ∧ Hy w h₂ ∧ x = h₁ * h₂ := by decide +kernel

theorem sum_a_aw : ∀ x : PermMod 6, (∑ i, Multiplicative.toAdd x i = 0) → ∃ h₁ h₂ : PermMod 6,
    Hy a h₁ ∧ Hy (a * w) h₂ ∧ x = h₁ * h₂ := by decide +kernel

theorem sum_w_aw : ∀ x : PermMod 6, (∑ i, Multiplicative.toAdd x i = 0) → ∃ h₁ h₂ : PermMod 6,
    Hy w h₁ ∧ Hy (a * w) h₂ ∧ x = h₁ * h₂ := by decide +kernel

@[expose] def Triple3 (u₁ u₂ u₃ : PermMod 6) : Prop :=
  u₁ ≠ u₂ → u₁ ≠ u₃ → u₂ ≠ u₃ → ∀ π : Perm (Fin 6),
    E2 (tau u₁) (tau u₂) π → E2 (tau u₁) (tau u₃) π → E2 (tau u₂) (tau u₃) π → π = 1

instance (u₁ u₂ u₃ : PermMod 6) : Decidable (Triple3 u₁ u₂ u₃) := by unfold Triple3; infer_instance

theorem triple3 : ∀ u₁ ∈ [a, w, a * w], ∀ u₂ ∈ [a, w, a * w], ∀ u₃ ∈ [a, w, a * w],
    Triple3 u₁ u₂ u₃ := by
  decide +kernel

theorem tau_a : tau a = swap 4 5 := by decide +kernel

theorem tau_w : tau w = swap 2 3 := by decide +kernel

theorem tau_aw : tau (a * w) = swap 0 1 := by decide +kernel

theorem a_mul_a_mul_w : a * (a * w) = w := by decide +kernel

theorem span_of {u : PermMod 6} (hu : u ∈ [a, w, a * w]) : ∀ x : PermMod 6, Hy u x →
    ∃ g₁ ∈ Gen u, ∃ g₂ ∈ Gen u, ∃ g₃ ∈ Gen u, x = g₁ * g₂ * g₃ := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact span_a
  · exact span_w
  · exact span_aw

theorem sum_of {u u' : PermMod 6} (hu : u ∈ [a, w, a * w]) (hu' : u' ∈ [a, w, a * w]) (hne : u ≠ u') :
    ∀ x : PermMod 6, (∑ i, Multiplicative.toAdd x i = 0) → ∃ h₁ h₂ : PermMod 6,
      Hy u h₁ ∧ Hy u' h₂ ∧ x = h₁ * h₂ := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu hu'
  rcases hu with rfl | rfl | rfl <;> rcases hu' with rfl | rfl | rfl
  · exact absurd rfl hne
  · exact sum_a_w
  · exact sum_a_aw
  · intro x hx
    obtain ⟨h₁, h₂, h1, h2, e⟩ := sum_a_w x hx
    exact ⟨h₂, h₁, h2, h1, by rw [e, mul_comm]⟩
  · exact absurd rfl hne
  · exact sum_w_aw
  · intro x hx
    obtain ⟨h₁, h₂, h1, h2, e⟩ := sum_a_aw x hx
    exact ⟨h₂, h₁, h2, h1, by rw [e, mul_comm]⟩
  · intro x hx
    obtain ⟨h₁, h₂, h1, h2, e⟩ := sum_w_aw x hx
    exact ⟨h₂, h₁, h2, h1, by rw [e, mul_comm]⟩
  · exact absurd rfl hne

theorem cent_of_gen {u : PermMod 6} (hu : u ∈ [a, w, a * w]) :
    ∀ π : Perm (Fin 6), (∀ g ∈ Gen u, permAct 6 π g = g) → π = 1 ∨ π = tau u := by
  intro π hπ
  have key : ∀ x : PermMod 6, Hy u x → permAct 6 π x = x := by
    intro x hx
    obtain ⟨g₁, h₁, g₂, h₂, g₃, h₃, rfl⟩ := span_of hu x hx
    simp only [map_mul, hπ g₁ h₁, hπ g₂ h₂, hπ g₃ h₃]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · rw [tau_a]; exact cent_a π key
  · rw [tau_w]; exact cent_w π key
  · rw [tau_aw]; exact cent_aw π key

end M6

end CFSG.Quasithin.ModC
