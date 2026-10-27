module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.ThetaPlaneAlpha

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open scoped Pointwise

@[expose] def ComponentLocalCoreOddConclusion {Q : Type*} [Group Q] (p : ℕ) (E : Subgroup Q)
    (t : Q) (L : Subgroup Q) : Prop :=
  ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
      thetaT p E : Subgroup Q) : Set Q) =
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ :
      Subgroup Q) : Set Q) * (thetaT p E : Set Q) ∧
  (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
      thetaT p E) ≤ Subgroup.normalizer (L : Set Q) ∧
  ¬ 2 ∣ (Subgroup.centralizer (L : Set Q)).relIndex
    (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set Q)), E⁆ ⊔
      thetaT p E)

@[expose] def OriginalLinearComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ n f : ℕ, ℓ.Prime → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL n ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalUnitaryComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ ℓ n f : ℕ, ℓ.Prime → StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalSymplecticOrthogonalComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ∀ (c : StatedLieTag), (c = .PSp ∨ c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) →
    ∀ ℓ n f : ℕ, ℓ.Prime → StatedClassicalModel (L ⧸ Subgroup.center L) c n ℓ f →
    p ∣ Nat.card (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

end CFSG.RankThree.PartOne
