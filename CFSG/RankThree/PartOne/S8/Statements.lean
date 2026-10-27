module

public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.Assembly.CatalogTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (Catalog ExceptionalRep)
open CFSG.Blueprint.NativeSporadic (SporadicRep)
open CFSG.SectionRank (IsKGroupCat)
open scoped Pointwise

@[expose] def TauCetiCatalogBridge : Prop :=
  CatalogImp InCatalog Catalog

@[expose] def OriginalCoprimeCatalogComponentLocalCoreCentralization : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    Catalog (L ⧸ Subgroup.center L) → ¬ p ∣ Nat.card (L ⧸ Subgroup.center L) →
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    p ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set (X ⧸ N))) ∧
      ComponentLocalCoreCentralizes p E t L

@[expose] def OriginalSporadicComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    SporadicRep (L ⧸ Subgroup.center L) → E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def OriginalExceptionalComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup (X ⧸ N), IsComponent L →
    ExceptionalRep (L ⧸ Subgroup.center L) → p ∣ Nat.card (L ⧸ Subgroup.center L) →
    E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
      Subgroup.normalizer (L : Set (X ⧸ N)) →
    ComponentLocalCoreOddConclusion p E t L

@[expose] def AlternatingComponentSelectedPrimeLocalCoreCentralization : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 3 < p → localRank p G ≤ 3 →
    ∀ E : Subgroup G, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 → ∀ L : Subgroup G, IsComponent L →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n))) →
    E ≤ Subgroup.normalizer (L : Set G) →
    inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G) →
    ComponentLocalCoreCentralizes p E t L

@[expose] def OriginalThetaFreeQuotientComponentActionPreparation : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroupCat X → evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    aschbacherSolvableCore p (X ⧸ N) = ⊥ →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 →
      localRank p X ≤ 3 ∧ localRank p (X ⧸ N) ≤ 3 ∧
      fittingSubgroup (X ⧸ N) = pCore p (X ⧸ N) ∧
      IsPGroup p (Subgroup.center (layer (X ⧸ N))) ∧
      (((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ ⊔
          thetaT p E : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ :
          Subgroup (X ⧸ N)) : Set (X ⧸ N)) * (thetaT p E : Set (X ⧸ N))) ∧
      Group.IsSolvable (localCoreProduct p E t) ∧ ¬ p ∣ Nat.card (localCoreProduct p E t) ∧
      localCoreProduct p E t ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ∧
      localCoreProduct p E t ≤ Subgroup.centralizer (fittingSubgroup (X ⧸ N) : Set (X ⧸ N)) ∧
      Nat.Coprime (Nat.card (localCoreProduct p E t)) (Nat.card (fittingSubgroup (X ⧸ N))) ∧
      ∀ L : Subgroup (X ⧸ N), IsComponent L →
        Catalog (L ⧸ Subgroup.center L) ∧ E ≤ Subgroup.normalizer (L : Set (X ⧸ N)) ∧
        ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ ≤
          Subgroup.normalizer (L : Set (X ⧸ N)) ∧
        (p ∣ Nat.card (L ⧸ Subgroup.center L) →
          inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))) ≤
            Subgroup.normalizer (L : Set (X ⧸ N)))

@[expose] def OriginalCatalogComponentLocalCoreOddAction : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroupCat X → evenRank X ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup X) [N.Normal], ¬ p ∣ Nat.card N →
    aschbacherSolvableCore p (X ⧸ N) = ⊥ →
    ∀ E : Subgroup (X ⧸ N), IsElementaryAbelian p E → Nat.card E = p ^ 2 →
    ∀ t ∈ E, t ≠ 1 →
      (((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ ⊔
          thetaT p E : Subgroup (X ⧸ N)) : Set (X ⧸ N)) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set (X ⧸ N))), E⁆ :
          Subgroup (X ⧸ N)) : Set (X ⧸ N)) * (thetaT p E : Set (X ⧸ N))) ∧
      ∀ L : Subgroup (X ⧸ N), IsComponent L →
        ComponentLocalCoreOddConclusion p E t L ∧
        ((¬ p ∣ Nat.card (L ⧸ Subgroup.center L) ∨
            E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) ≠ ⊥) →
          localCoreProduct p E t ≤ Subgroup.centralizer (L : Set (X ⧸ N)))

end CFSG.RankThree.PartOne
