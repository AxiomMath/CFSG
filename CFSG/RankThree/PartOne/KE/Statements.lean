module

public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ChevalleyExceptionalModel ReeTitsModel SuzukiModel)
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

@[expose] noncomputable def localCoreProductImage {G : Type*} [Group G] (p : ℕ) (E : Subgroup G)
    (t : G) (L : Subgroup G) : Subgroup (MulAut (L ⧸ Subgroup.center L)) :=
  ((localCoreProduct p E t).subgroupOf (Subgroup.normalizer (L : Set G))).map
    (Finkelstein1977.automizer L)

@[expose] def ComponentLocalCoreOddImage {G : Type*} [Group G] (p : ℕ) (E : Subgroup G) (t : G)
    (L : Subgroup G) : Prop :=
  ((localCoreProduct p E t : Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ :
        Subgroup G) : Set G) * (thetaT p E : Set G) ∧
    localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G) ∧
    ¬ 2 ∣ Nat.card (localCoreProductImage p E t L) ∧
    CFSG.Quasithin.twoPrimeResidual (localCoreProduct p E t) ≤ Subgroup.centralizer (L : Set G)

@[expose] def G2CrossPrimeActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ p → 1 ≤ f →
    ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddConclusion p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G))

@[expose] def F4CompleteActualQuotientComponentOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N → localRank p X ≤ 3 →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ (t : X ⧸ N) (ht : t ∈ E), t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f →
    ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .F4 ℓ f →
    ∀ hEL : E ≤ Subgroup.normalizer (L : Set (X ⧸ N)),
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L ∧
      ((¬ p ∣ Nat.card (L ⧸ Subgroup.center L) ∨
          E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) ≠ ⊥ ∨
          Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set (X ⧸ N)))

@[expose] def OriginalE6AndTwistedE6ComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ τ : StatedLieTag, (τ = .E6 ∨ τ = .twistedE6) →
    ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalE7ComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .E7 ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalE8ComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .E8 ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalTrialityComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f →
    ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .trialityD4 ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def SuzukiNormalizedComponentLocalCoreProductOddImage : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup H, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup H, IsComponent L →
    ∀ ℓ f : ℕ, SuzukiModel (L ⧸ Subgroup.center L) ℓ f →
    E ≤ Subgroup.normalizer (L : Set H) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)) ≤
      Subgroup.normalizer (L : Set H) →
    ComponentLocalCoreOddImage p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set H) ≠ ⊥ →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set H))

@[expose] def SmallReeNormalizedComponentLocalCoreProductOddImage : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup H, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup H, IsComponent L →
    ∀ ℓ f : ℕ, ReeTitsModel (L ⧸ Subgroup.center L) .twistedG2 ℓ f →
    E ≤ Subgroup.normalizer (L : Set H) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)) ≤
      Subgroup.normalizer (L : Set H) →
    ComponentLocalCoreOddImage p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set H) ≠ ⊥ →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set H))

@[expose] def LargeReeAllActorsActualComponentLocalCoreProductOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ (t : G) (ht : t ∈ E), t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ∀ ℓ f : ℕ, ReeTitsModel (L ⧸ Subgroup.center L) .twistedF4 ℓ f →
    ∀ hEL : E ≤ Subgroup.normalizer (L : Set G),
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddConclusion p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G))

@[expose] def TitsNormalizedComponentLocalCoreProductOddImage : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ∀ ℓ f : ℕ, ReeTitsModel (L ⧸ Subgroup.center L) .Tits ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddImage p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) = ⊥ → p = 5)

end CFSG.RankThree.PartOne
