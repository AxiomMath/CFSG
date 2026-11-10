module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Induction of class functions

The class function on `G` induced from a class function of a subgroup `H`,
and its support property.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Theory.Character

universe u

/-- The class function on `G` induced from a class function of the subgroup `H`. -/
@[expose] public def inducedClassFunction {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ClassFunction (↥H)) : ClassFunction G := by
  classical
  exact fun g => (Nat.card (↥H) : ℂ)⁻¹ * ∑ x : G,
    if hx : x⁻¹ * g * x ∈ H then φ ⟨x⁻¹ * g * x, hx⟩ else 0

/-- The induced function vanishes on elements with no conjugate in `H`. -/
public lemma inducedClassFunction_supportedOn {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (φ : ClassFunction (↥H)) (g : G) (hg : ∀ x : G, x⁻¹ * g * x ∉ H) :
    inducedClassFunction H φ g = 0 := by
  classical
  unfold inducedClassFunction
  simp [hg]

end CFSG.Theory.Character
