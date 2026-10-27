module

public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def UnitaryDefiningPrimeActualComponentLocalCoreProductCentralizes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N → localRank p X ≤ 3 →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L → ∀ n f : ℕ,
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n p f →
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreCentralizes p E t L

@[expose] def UnitaryNonsplitInnerActualComponentCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 3 ≤ n → ¬ p ∣ ℓ ^ f + 1 →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    E ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    actualPlane L E ≤
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range →
    ComponentLocalCoreCentralizes p E t L

@[expose] def NonsplitUnitaryNoninnerActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 3 ≤ n → ¬ p ∣ ℓ ^ f + 1 →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
    ComponentLocalCoreOddResidual p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤
        Subgroup.centralizer (L : Set G))

@[expose] def HigherUnitaryAllPlaneActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 ≤ n → n < p → ℓ ≠ p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddConclusion p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G))

@[expose] def EvenUnitaryFiveActualComponentLocalCoreProductOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ),
    ∀ E : Subgroup G, IsElementaryAbelian 5 E → Nat.card E = 5 ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 5 2 f → 5 ∣ 2 ^ f + 1 →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore 5) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddConclusion 5 E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct 5 E t ≤
        Subgroup.centralizer (L : Set G))

end CFSG.RankThree.PartOne
