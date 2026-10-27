module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.Compatible
import CFSG.LocalAnalysis.SolvableSignalizer.LocalCompleteness
import CFSG.LocalAnalysis.SolvableSignalizer.MinimalCounterexample

public section

universe u v

namespace CFSG.SolvableSignalizer

theorem Datum.isComplete_of_two {A : Type u} {G : Type v} [CommGroup A] [Finite A] [Group G]
    [Finite G] {α : A →* MulAut G} {θ : A → Subgroup G} (d : Datum 2 α θ)
    (hA : 8 ≤ Nat.card A) : IsComplete 2 α θ := by
  suffices h : ∀ n : ℕ, ∀ (A : Type u) (G : Type v) [CommGroup A] [Finite A] [Group G]
      [Finite G] (α : A →* MulAut G) (θ : A → Subgroup G), Datum 2 α θ → 8 ≤ Nat.card A →
      Nat.card G + (spectrum θ).ncard = n → IsComplete 2 α θ from
    h _ A G α θ d hA rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A G _ _ _ _ α θ d hA hn
    by_contra hinc
    refine hinc (isComplete_of_locallyComplete_of_two α θ d hA ?_)
    refine (locallyComplete_of_minimal_incomplete d (by simpa using hA) hinc ?_).1
    intro A' G' _ _ _ _ α' θ' d' hA' hlt
    exact ih _ (hn ▸ hlt) A' G' α' θ' d' (by simpa using hA') rfl

theorem two_signalizer_completeness (G : Type*) [Group G] [Finite G]
    (A : Type*) [CommGroup A] [Finite A] (hexp : ∀ a : A, a ^ 2 = 1) (hcard : 8 ≤ Nat.card A)
    (α : A →* MulAut G) (θ : A → Subgroup G)
    (hinv : ∀ a : A, a ≠ 1 → ∀ b : A, (θ a).map (α b).toMonoidHom = θ a)
    (hsolv : ∀ a : A, a ≠ 1 → Group.IsSolvable (θ a))
    (hodd : ∀ a : A, a ≠ 1 → Odd (Nat.card (θ a)))
    (hcent : ∀ a : A, a ≠ 1 → ∀ g ∈ θ a, α a g = g)
    (hbal : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∀ g ∈ θ a, α b g = g → g ∈ θ b) :
    let Θ : Subgroup G := ⨆ (a : A) (_ : a ≠ 1), θ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧ Odd (Nat.card Θ) ∧
      ∀ a : A, a ≠ 1 → ∀ g : G, (g ∈ Θ ∧ α a g = g ↔ g ∈ θ a) := by
  have d : Datum 2 α θ :=
    { prime := Nat.prime_two
      exponent := hexp
      rank_two := by norm_num; omega
      invariant := hinv
      solvable := hsolv
      coprime := fun a ha => Nat.coprime_two_left.mpr (hodd a ha)
      central := fun a ha g hg => hcent a ha g hg
      balance := fun a b ha hb g hg => hbal a b ha hb g hg.1 hg.2 }
  obtain ⟨hinvΘ, hsolvΘ, hcop, hfix⟩ :=
    fixedIn_completion_of_isComplete d (d.isComplete_of_two hcard)
  intro Θ
  refine ⟨hinvΘ, hsolvΘ, Nat.coprime_two_left.mp hcop, fun a ha g => ?_⟩
  rw [← hfix a ha]
  rfl

end CFSG.SolvableSignalizer
