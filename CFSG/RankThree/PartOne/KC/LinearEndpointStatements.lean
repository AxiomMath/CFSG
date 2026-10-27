module

public import CFSG.RankThree.PartOne.KC.TargetStatements
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped Pointwise

@[expose] noncomputable def localCoreProduct {G : Type*} [Group G] (p : ℕ) (E : Subgroup G)
    (t : G) : Subgroup G :=
  ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ ⊔
    thetaT p E

@[expose] def ComponentLocalCoreCentralizes {G : Type*} [Group G] (p : ℕ) (E : Subgroup G)
    (t : G) (L : Subgroup G) : Prop :=
  ((localCoreProduct p E t : Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆ :
        Subgroup G) : Set G) * (thetaT p E : Set G) ∧
    localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G) ∧
    ⁅⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)), E⁆, L⁆ = ⊥ ∧
    ⁅thetaT p E, L⁆ = ⊥ ∧ localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)

@[expose] def ComponentLocalCoreOddResidual {G : Type*} [Group G] (p : ℕ) (E : Subgroup G)
    (t : G) (L : Subgroup G) : Prop :=
  ComponentLocalCoreOddConclusion p E t L ∧
    CFSG.Quasithin.twoPrimeResidual (localCoreProduct p E t) ≤ Subgroup.centralizer (L : Set G)

@[expose] def LinearDefiningPrimeActualComponentLocalCoreProductCentralizes : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N → localRank p X ≤ 3 →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L → ∀ n f : ℕ,
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n p f →
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreCentralizes p E t L

@[expose] def LinearTwoNormalizedComponentLocalCoreProductOddImage : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    ∀ (ℓ f : ℕ) (k : Type) [Field k] [Finite k], ℓ.Prime → 1 ≤ f → Nat.card k = ℓ ^ f →
    4 ≤ ℓ ^ f → Nonempty ((L ⧸ Subgroup.center L) ≃* projectiveSL 2 k) →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreOddResidual p E t L ∧
      (p = ℓ → localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) ∧
      (E ⊓ Subgroup.centralizer (L : Set G) = ⊥ → p ≠ ℓ → p ∣ f)

@[expose] def LinearNonsplitInnerActualComponentCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 3 ≤ n → ¬ p ∣ ℓ ^ f - 1 →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    E ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    actualPlane L E ≤
      (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range →
    ComponentLocalCoreCentralizes p E t L

@[expose] def NonsplitLinearNoninnerActualComponentOddAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 3 ≤ n → ¬ p ∣ ℓ ^ f - 1 →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      ¬ actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
    ComponentLocalCoreOddResidual p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤
        Subgroup.centralizer (L : Set G))

@[expose] def LinearBelowPrimeNoninnerOrSplitNormalizedComponentOddAction : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (p ℓ f n : ℕ), p.Prime → 3 < p → ℓ.Prime → ℓ ≠ p →
    1 ≤ f → 3 ≤ n → n < p →
    ∀ E : Subgroup H, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup H, IsComponent L →
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f →
    E ≤ Subgroup.normalizer (L : Set H) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)) ≤
      Subgroup.normalizer (L : Set H) →
    (E ⊓ Subgroup.centralizer (L : Set H) ≠ ⊥ ∨
      ¬ actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ∨
      p ∣ ℓ ^ f - 1) →
    ComponentLocalCoreOddResidual p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set H) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set H))

end CFSG.RankThree.PartOne
