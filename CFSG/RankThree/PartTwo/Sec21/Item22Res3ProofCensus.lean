module

public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def Inspection228ListMono :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A K K₀ : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    (∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
      (starOf A X).map (coordGL f) ≤ KFacts.KP14.monomial) →
    (∀ ρ ∈ starOf A X, ¬ IsTransvectionOn ρ) →
    ∀ ρ ∈ starOf A X, IsReflectionOn ρ →
      K ≤ K₀ → K₀ ≤ X → K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) →
      (∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀) →
      (K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2) →
      Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 0 < m → Even m →
        List228 (X ⧸ aschbacherSolvableCore 3 X) m

open Item228ResProof

variable {G : Type} [Group G]

end CFSG.RankThree.PartTwo.Sec21
