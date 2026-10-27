module

public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open scoped commutatorElement

@[expose] def EvenLieFiveRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.EvenLieType X → Census3.TheoremThreeList X →
    ∀ q : ℕ, (q = 3 ∨ q = 7) → ∀ D : Subgroup X, CFSG.IsElementaryAbelian q D →
      Nat.card D = q ^ 5 → False

@[expose] def EvenLieNoQD32 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
    CFSG.Blueprint.EvenLieType X → Census3.TheoremThreeList X →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → ∀ α : MulAut X, α ^ 5 = 1 →
      ∀ Y R : Subgroup X, (∀ y ∈ Y, y ^ q = 1) →
      (∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1) → IsPGroup 2 R →
      R ≤ Subgroup.normalizer (Y : Set X) → (∀ y ∈ Y, α y ∈ Y) → (∀ r ∈ R, α r ∈ R) →
      (∃ r ∈ R, α r * r⁻¹ ∉ Subgroup.centralizer (Y : Set X)) →
      ∀ ψ : ↥R →* QD32, Function.Surjective ψ →
        (∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ Subgroup.centralizer (Y : Set X)) → False

@[expose] def FiveNoncentralExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G) (c : G) (q : ℕ) (D R : Subgroup G)
    (e : G) (K : Subgroup G), FiveSuccessorData A L c q D R e K →
    ⁅thetaQuotientCentralizer 5 A L, D⁆ ≠ ⊥ →
    ∀ K' ∈ sectionTenZeroStar 5 A, K ≤ K' →
      CFSG.Blueprint.EvenLieType (↥K' ⧸ Subgroup.center ↥K') →
      Census3.TheoremThreeList (↥K' ⧸ Subgroup.center ↥K') → False

end CFSG.RankThree.PartOne.F106
