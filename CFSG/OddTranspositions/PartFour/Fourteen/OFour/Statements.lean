module

public import CFSG.OddTranspositions.PartFour.Fourteen.Statements
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

@[expose] def Theorem4OFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) →
    (∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      CFSG.LocalAnalysis.WeakClosure81.IsOrthReflection
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) →
    AscList G D

structure O4CaseAFacts (X : Type) [Group X] (Θ : Set X) : Prop where
  index_two : (commutator X).index = 2
  perfect : ⁅commutator X, commutator X⁆ = commutator X
  cover : ∀ (E : Type) [Group E] [Finite E] (p : E →* commutator X), Function.Surjective p →
    p.ker ≤ Subgroup.center E → commutator E = ⊤ → p.ker = ⊥
  primitive : ∀ B : Set X, B ⊆ Θ → B.Nonempty →
    (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨ Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
    B.Subsingleton ∨ B = Θ
  triple : ∃ Λ ⊆ Θ, (∀ a ∈ Λ, ∀ b ∈ Λ, Commute a b) ∧
    ∃ v ∈ Λ, v ∈ Subgroup.closure (Λ \ {v})

end CFSG.OddTranspositions.PartFour
