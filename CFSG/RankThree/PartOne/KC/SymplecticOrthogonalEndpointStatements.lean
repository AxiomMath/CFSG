module

public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

@[expose] def ComponentLocalCoreNormalizes {G : Type*} [Group G] (p : ℕ) (E : Subgroup G)
    (t : G) (L : Subgroup G) : Prop :=
  ((localCoreProduct p E t : Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ :
        Subgroup G) : Set G) * (thetaT p E : Set G) ∧
    localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G)

@[expose] def SymplecticDefiningPrimeActualComponentLocalCoreProductCentralizes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N → localRank p X ≤ 3 →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L → ∀ n f : ℕ,
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n p f →
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreCentralizes p E t L

@[expose] def SymplecticActualRankInnerPlaneLocalCoreProductCentralizes : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p ℓ f r : ℕ), p.Prime → 3 < p → localRank p Q ≤ 3 →
    2 ≤ r → ℓ ≠ p →
    ∀ E : Subgroup Q, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup Q, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp r ℓ f →
    E ≤ Subgroup.normalizer (L : Set Q) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)) ≤
      Subgroup.normalizer (L : Set Q) →
    ComponentLocalCoreNormalizes p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set Q) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set Q))

@[expose] def SymplecticNoninnerActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f r : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 2 ≤ r →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSp r ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
    ComponentLocalCoreOddResidual p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤
        Subgroup.centralizer (L : Set G))

@[expose] def OrthogonalActualRankInnerPlaneLocalCoreProductCentralizes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → localRank p G ≤ 3 →
    ℓ ≠ p → ∀ c : StatedLieTag, (c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) c n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreNormalizes p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G))

@[expose] def OrthogonalNoninnerActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    ∀ c : StatedLieTag, (c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) c n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
    ComponentLocalCoreOddResidual p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤
        Subgroup.centralizer (L : Set G))

end CFSG.RankThree.PartOne
