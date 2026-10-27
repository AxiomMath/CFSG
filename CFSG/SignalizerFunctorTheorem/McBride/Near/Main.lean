module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.Final

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

open Near in
private theorem near_main_aux
    (p : ℕ) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G], Nat.card G = n →
      ∀ (A : Subgroup G) (θ : G → Subgroup G), NearHyp p A θ →
        IsCompleteIn (signalizers p A θ (NearASolvable p A)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn A θ hθ
    by_contra hnc
    classical
    let S : Set ℕ := {s | ∃ θ' : G → Subgroup G, NearHyp p A θ' ∧
      ¬ IsCompleteIn (signalizers p A θ' (NearASolvable p A)) ∧ size A θ' = s}
    have hS : S.Nonempty := ⟨size A θ, θ, hθ, hnc, rfl⟩
    have hspec := Nat.find_spec hS
    obtain ⟨θ₀, hθ₀, hnc₀, hsize₀⟩ := hspec
    refine Counterexample.false (p := p) (A := A) (θ := θ₀) ?_
    refine ⟨hθ₀, hnc₀, ?_, ?_⟩
    · intro H _ _ hlt A' θ' hh
      exact ih (Nat.card H) (hn ▸ hlt) H rfl A' θ' hh
    · intro θ'' hh hnc''
      rw [hsize₀]
      exact Nat.find_min' hS ⟨θ'', hh, hnc'', rfl⟩

theorem near_main
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hcard : Nat.card A = p ^ 3)
    {θ : G → Subgroup G} (hθ : IsFunctor p A θ)
    (hns : ∀ a ∈ A, a ≠ 1 → NearASolvable p A (θ a)) :
    IsCompleteIn (signalizers p A θ (NearASolvable p A)) :=
  near_main_aux p (Nat.card G) G rfl A θ ⟨hp, hp2, hA, hcard, hθ, hns⟩

end CFSG.SignalizerFunctorTheorem.McBride
