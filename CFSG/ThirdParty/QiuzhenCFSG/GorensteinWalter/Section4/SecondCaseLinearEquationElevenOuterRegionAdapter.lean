module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenOuterRegion
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equation (11): outer-region predicate adapter

The outer-region producer records its family with the conjunction ordered as
`Y ≤ P ⊔ E ∧ Y ≠ P ∧ conjugate`.  The generic region inequality instead
expects `conjugate ∧ Y ≠ P ∧ Y ≤ P ⊔ E`.  This module provides the exact
subtype-cardinality adapter between those equivalent predicates.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The outer-region lower bound in the predicate orientation consumed by
`secondCase_linearEquation11_region_inequality`. -/
public theorem secondCase_linearEquation11_outer_region_hXs
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    {p1 : ℕ}
    (hLines : Nat.card (secondCase_linesIn G post.od.P post.od.P0) = p1 - 1)
    (hPinterE : post.od.P ⊓ d.E = ⊥) :
    (p1 - 1) * Nat.card K * post.equation9.k' ≤
      Nat.card {X : Subgroup G //
        (∃ g : G, X = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
        X ≠ post.od.P ∧ X ≤ post.od.P ⊔ d.E} := by
  have h := secondCase_linearEquation11_outer_region c w d K post hLines hPinterE
  let e : {Y : Subgroup G //
      Y ≤ post.od.P ⊔ d.E ∧ Y ≠ post.od.P ∧
        ∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom} ≃
      {X : Subgroup G //
        (∃ g : G, X = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
        X ≠ post.od.P ∧ X ≤ post.od.P ⊔ d.E} :=
    Equiv.subtypeEquiv (Equiv.refl (Subgroup G)) (by
      intro X
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3, h2, h1⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h3, h2, h1⟩)
  calc
    (p1 - 1) * Nat.card K * post.equation9.k' ≤
        Nat.card {Y : Subgroup G //
          Y ≤ post.od.P ⊔ d.E ∧ Y ≠ post.od.P ∧
            ∃ g : G, Y = post.od.P.map (MulAut.conj g).toMonoidHom} := h
    _ = Nat.card {X : Subgroup G //
        (∃ g : G, X = post.od.P.map (MulAut.conj g).toMonoidHom) ∧
        X ≠ post.od.P ∧ X ≤ post.od.P ⊔ d.E} :=
      Nat.card_congr e

end CFSG.GorensteinWalter
