module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.HyperPlaneCube

public section

open CFSG.LieType.SeitzGeneration CFSG.Open

namespace CFSG.RankThree.PartTwo.Sec4.E27

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem hyperGen_of_two_lines {K E : Subgroup Y} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {f₁ f₂ : Y} (hf₁E : f₁ ∈ E) (hf₂E : f₂ ∈ E)
    (hf₁ : f₁ ≠ 1) (hf₂ : f₂ ≠ 1) {L₁ L₂ : Subgroup Y} (hL₁K : L₁ ≤ K) (hL₂K : L₂ ≤ K)
    (hL₁f : ∀ l ∈ L₁, f₁ * l = l * f₁) (hL₂f : ∀ l ∈ L₂, f₂ * l = l * f₂)
    (hL₁ : L₁ ≤ Subgroup.closure
      {l | l ∈ L₁ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₁ ∧ x * l = l * x})
    (hL₂ : L₂ ≤ Subgroup.closure
      {l | l ∈ L₂ ∧ ∃ x ∈ E, x ∉ Subgroup.zpowers f₂ ∧ x * l = l * x})
    (hgen : K ≤ L₁ ⊔ L₂) : HyperGen p K E := by
  have hp : p.Prime := Fact.out
  rw [hyperGen_iff_le]
  exact hgen.trans (sup_le (le_hyperClosure_of_plane hp hE hcard hf₁E hf₁ hL₁K hL₁f hL₁)
    (le_hyperClosure_of_plane hp hE hcard hf₂E hf₂ hL₂K hL₂f hL₂))

end CFSG.RankThree.PartTwo.Sec4.E27
