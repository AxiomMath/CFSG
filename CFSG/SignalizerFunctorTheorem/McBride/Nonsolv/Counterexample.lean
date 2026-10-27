module

public import CFSG.SignalizerFunctorTheorem.McBride.Defs

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

structure TheoremAHyp (p : ℕ) {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (θ : G → Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elemAbelian : IsElemAbelian p A
  card : Nat.card A = p ^ 3
  isFunctor : IsFunctor p A θ
  hypC : ∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (θ a)

structure Counterexample (p : ℕ) {G : Type u} [Group G] [Finite G] (A : Subgroup G)
    (θ : G → Subgroup G) : Prop where
  hyp : TheoremAHyp p A θ
  notComplete : ¬ IsCompleteIn (signalizers p A θ (signalizerMcBrideHypothesisB p))
  ih : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ (A' : Subgroup H) (θ' : H → Subgroup H), TheoremAHyp p A' θ' →
      IsCompleteIn (signalizers p A' θ' (signalizerMcBrideHypothesisB p))
  minimal : ∀ θ' : G → Subgroup G, TheoremAHyp p A θ' →
    ¬ IsCompleteIn (signalizers p A θ' (signalizerMcBrideHypothesisB p)) →
      size A θ ≤ size A θ'

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem complete_of_size_lt (h : Counterexample p A θ) {θ' : G → Subgroup G}
    (hθ' : TheoremAHyp p A θ') (hlt : size A θ' < size A θ) :
    IsCompleteIn (signalizers p A θ' (signalizerMcBrideHypothesisB p)) := by
  by_contra hnc
  exact absurd (h.minimal θ' hθ' hnc) (not_le.mpr hlt)

end Counterexample

theorem complete_of_no_counterexample (p : ℕ)
    (h : ∀ (G : Type u) [Group G] [Finite G] (A : Subgroup G) (θ : G → Subgroup G),
      Counterexample p A θ → False)
    {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
    (hθ : TheoremAHyp p A θ) :
    IsCompleteIn (signalizers p A θ (signalizerMcBrideHypothesisB p)) := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G A θ with
  | _ n ihn =>
    by_contra hnc
    classical
    let S : Set ℕ := {m | ∃ θ' : G → Subgroup G, TheoremAHyp p A θ' ∧
      ¬ IsCompleteIn (signalizers p A θ' (signalizerMcBrideHypothesisB p)) ∧ size A θ' = m}
    have hS : ∃ m, m ∈ S := ⟨_, θ, hθ, hnc, rfl⟩
    obtain ⟨θ₀, hθ₀, hnc₀, hsize⟩ := Nat.find_spec hS
    refine h G A θ₀ ⟨hθ₀, hnc₀, ?_, ?_⟩
    · intro H _ _ hlt A' θ' hθ'
      exact ihn (Nat.card H) (hn ▸ hlt) hθ' rfl
    · intro θ' hθ' hnc'
      rw [hsize]
      exact Nat.find_min' hS ⟨θ', hθ', hnc', rfl⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
