module

public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG

namespace FiveTransitive.InvolutionPairFixerTransitivity

open MulAction

theorem transitive_of_cross_pairs
    {G X : Type*} [Group G] [MulAction G X] (a : G) (ha : a * a = 1)
    (hcross : ∀ t : Fin 4 ↪ X,
      a • t 0 = t 1 → a • t 1 = t 0 → a • t 2 = t 3 → a • t 3 = t 2 →
      ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧ (g • t 0 = t 2 ∨ g • t 0 = t 3)) :
    ∀ x y : X, x ∉ fixedBy X a → y ∉ fixedBy X a →
      ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧ g • x = y := by
  intro x y hx hy
  have haa (z : X) : a • (a • z) = z := by rw [← mul_smul, ha, one_smul]
  have haFix : ∀ z ∈ fixedBy X a, a • z = z := fun _ hz => hz
  by_cases hxy : x = y
  · exact ⟨1, fun _ _ => one_smul _ _, by simpa only [one_smul] using hxy⟩
  by_cases hay : a • x = y
  · exact ⟨a, haFix, hay⟩
  have hax : a • x ≠ x := hx
  have hayy : a • y ≠ y := hy
  have hxay : x ≠ a • y := by
    intro he
    have hh := congrArg (fun z : X => a • z) he
    rw [haa] at hh
    exact hay hh
  have haxay : a • x ≠ a • y := fun h => hxy ((MulAction.injective a) h)
  let t : Fin 4 ↪ X := ⟨![x, a • x, y, a • y], by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hxy, Ne.symm hxy, hax, hax.symm, hay, Ne.symm hay,
        hayy, hayy.symm, hxay, hxay.symm, haxay, haxay.symm]⟩
  obtain ⟨g, hgfix, hg⟩ := hcross t rfl (haa x) rfl (haa y)
  rcases hg with hg | hg
  · exact ⟨g, hgfix, hg⟩
  · refine ⟨a * g, ?_, ?_⟩
    · intro z hz
      rw [mul_smul, hgfix z hz, haFix z hz]
    · rw [mul_smul, show g • x = a • y from hg, haa]

end FiveTransitive.InvolutionPairFixerTransitivity

end CFSG
