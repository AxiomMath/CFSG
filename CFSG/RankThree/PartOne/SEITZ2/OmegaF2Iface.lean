module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaFrame
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Triple

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

structure F2Triple (Q : QuadraticForm K V) where
  x : Fin 3 → V
  y : Fin 3 → V
  Q_x : ∀ i, Q (x i) = 0
  Q_y : ∀ i, Q (y i) = 0
  polar_xx : ∀ i j, polar Q (x i) (x j) = 0
  polar_xy : ∀ i j, polar Q (x i) (y j) = if i = j then 1 else 0

variable {Q : QuadraticForm K V}

@[expose] def F2Triple.Generic (T : F2Triple Q) (u w : V) : Prop :=
  Phi Q u w (T.x 0) (T.x 1) ≠ 0 ∧
    ∀ l₀ l₁ : K, (l₀ = 0 ∨ l₀ = 1) → (l₁ = 0 ∨ l₁ = 1) →
      ¬ (polar Q (T.x 2 + l₀ • T.x 0 + l₁ • T.x 1) u = 0 ∧
        polar Q (T.x 2 + l₀ • T.x 0 + l₁ • T.x 1) w = 0)

end Triple

theorem mem_subfield_two_iff {K : Type} [Field K] {k : Subfield K} (hk : Nat.card k = 2) {x : K} :
    x ∈ k ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro hx
    obtain ⟨a, b, -, hall⟩ := Nat.card_eq_two_iff.1 hk
    have hmem : ∀ e : k, e = a ∨ e = b := fun e => by
      have : e ∈ ({a, b} : Set k) := by rw [hall]; trivial
      simpa using this
    by_contra hcon
    push Not at hcon
    have h01 : (⟨0, k.zero_mem⟩ : k) ≠ ⟨1, k.one_mem⟩ := fun h => by
      have := congrArg Subtype.val h
      simp at this
    have h0x : (⟨0, k.zero_mem⟩ : k) ≠ ⟨x, hx⟩ := fun h => hcon.1 (congrArg Subtype.val h).symm
    have h1x : (⟨1, k.one_mem⟩ : k) ≠ ⟨x, hx⟩ := fun h => hcon.2 (congrArg Subtype.val h).symm
    rcases hmem ⟨0, k.zero_mem⟩ with h0 | h0 <;> rcases hmem ⟨1, k.one_mem⟩ with h1 | h1 <;>
      rcases hmem ⟨x, hx⟩ with h2 | h2 <;>
      first
      | exact h01 (h0.trans h1.symm)
      | exact h0x (h0.trans h2.symm)
      | exact h1x (h1.trans h2.symm)
  · rintro (rfl | rfl)
    exacts [k.zero_mem, k.one_mem]

@[expose] def OmegaF2Core : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (k : Subfield K) (p : ℕ), p.Prime → p ≠ 2 → Nat.card K = 2 ^ p →
    Nat.card k = 2 → ∀ (T : F2Triple Q) (u w : V), Q u = 0 → Q w = 0 → polar Q u w = 0 →
    T.Generic u w → ∀ M : Subgroup (V ≃ₗ[K] V), eichler Q u w ∈ M →
    eichler Q (T.x 0) (T.x 1) ∈ M → eichler Q (T.x 0) (T.x 2) ∈ M →
    eichler Q (T.x 1) (T.x 2) ∈ M → (∀ i j, i ≠ j → eichler Q (T.x i) (T.y j) ∈ M) →
    ∀ t : K, eichler Q (T.x 0) (t • T.x 1) ∈ M

end CFSG.RankThree.PartOne.SEITZ2
