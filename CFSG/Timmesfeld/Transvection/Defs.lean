module

public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H]

structure IsTransvectionClass (Δ : Set (Subgroup H)) : Prop where
  root : IsRootClass Δ
  noSpecial : ∀ A ∈ Δ, ∀ B ∈ Δ, ¬ Special Δ A B

@[expose] def PointsDetermined (Δ : Set (Subgroup H)) : Prop :=
  ∀ A ∈ Δ, ∀ B ∈ Δ, (∀ C ∈ Δ, Commuting A C ↔ Commuting B C) → A = B

@[expose] def ThickLines (Δ : Set (Subgroup H)) : Prop :=
  ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commuting A B →
    ∃ C ∈ Δ, C ≠ A ∧ C ≠ B ∧ ∀ D ∈ Δ, Commuting D A → Commuting D B → Commuting D C

structure TransvectionHyp (H : Type*) [Group H] (Δ : Set (Subgroup H)) : Prop where
  finite : Finite H
  cls : IsTransvectionClass Δ
  points : PointsDetermined Δ
  center : Subgroup.center H = ⊥
  rank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B
  small : (∃ A ∈ Δ, Nat.card A = 2) → IsSimpleGroup (commutator H) ∧ ThickLines Δ

namespace IsTransvectionClass

variable {Δ : Set (Subgroup H)}

theorem commuting_or_opposite (hΔ : IsTransvectionClass Δ) {A B : Subgroup H} (hA : A ∈ Δ)
    (hB : B ∈ Δ) (hAB : A ≠ B) : Commuting A B ∨ Opposite A B := by
  rcases hΔ.root.rel A hA B hB hAB with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hΔ.noSpecial A hA B hB)

theorem noIsolated (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hrank : ∃ A ∈ Δ, ∃ B ∈ Δ, A ≠ B ∧ Commuting A B) : NoIsolated Δ := by
  by_contra hno
  simp only [NoIsolated, not_forall, not_exists, not_and] at hno
  obtain ⟨A₀, hA₀, hA₀opp⟩ := hno
  have hA₀c : ∀ B ∈ Δ, Commuting A₀ B := by
    intro B hB
    by_cases hBA : A₀ = B
    · subst hBA
      exact hΔ.root.commuting_self hA₀
    · rcases hΔ.commuting_or_opposite hA₀ hB hBA with h | h
      · exact h
      · exact absurd h (hA₀opp B hB)
  have hall : ∀ A ∈ Δ, ∀ B ∈ Δ, Commuting A B := by
    intro A hA B hB
    obtain ⟨g, rfl⟩ := hΔ.root.exists_conjSub_eq hA₀ hA
    have hB' : conjSub B g⁻¹ ∈ Δ := hΔ.root.conjSub_mem hB g⁻¹
    have h := (hA₀c _ hB').conjSub g
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h
  obtain ⟨A, hA, B, hB, hAB, -⟩ := hrank
  exact hAB (hpts A hA B hB fun C hC => ⟨fun _ => hall B hB C hC, fun _ => hall A hA C hC⟩)

end IsTransvectionClass

end CFSG.Timmesfeld.Transvection
