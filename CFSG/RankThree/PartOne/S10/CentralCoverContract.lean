module

public import CFSG.RankThree.CentralCover.SteinbergBNOddExtensionRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.CentralCover

abbrev centerQuotientMap (X : Type*) [Group X] : X →* X ⧸ Subgroup.center X :=
  QuotientGroup.mk' (Subgroup.center X)

abbrev centerPCore (p : ℕ) (X : Type) [Group X] : Subgroup X :=
  inSubgroup (CFSG.pCore p) (Subgroup.center X)

@[expose] def CentralOddExtensionExactlyOneCase {P : Type*} [Group P] (A : Subgroup P) [A.Normal]
    (p d : ℕ) : Prop :=
  (CentralOddExtensionCaseOne A p d ∨ CentralOddExtensionCaseTwo A p d ∨
      CentralOddExtensionCaseThree A p d) ∧
    ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseTwo A p d) ∧
    ¬ (CentralOddExtensionCaseOne A p d ∧ CentralOddExtensionCaseThree A p d) ∧
    ¬ (CentralOddExtensionCaseTwo A p d ∧ CentralOddExtensionCaseThree A p d)

@[expose] def SourceFiveTwoCentralCoverLocalRankFourObstruction : Prop :=
  ∀ (H : Type) [Group H] [Finite H], evenRank H ≤ 3 → ∀ X : Subgroup H,
    (∀ U : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 2 U → U ≠ ⊥ →
      ∃ T : Subgroup ↥X,
        T ≤ U.comap (centerQuotientMap ↥X) ∧ IsPGroup 2 T ∧
        (∀ T' : Subgroup ↥X, T' ≤ U.comap (centerQuotientMap ↥X) → IsPGroup 2 T' → T' ≤ T) ∧
        T.map (centerQuotientMap ↥X) = U ∧
        U.comap (centerQuotientMap ↥X) = Subgroup.center ↥X ⊔ T ∧
        (Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X))).comap
            (centerQuotientMap ↥X) = Subgroup.normalizer (T : Set ↥X) ∧
        (Subgroup.normalizer (T : Set ↥X)).map (centerQuotientMap ↥X) =
          Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X)) ∧
        Subgroup.center ↥X ≤ Subgroup.normalizer (T : Set ↥X) ∧
        ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup (↥X ⧸ Subgroup.center ↥X),
          E ≤ Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X)) →
          IsElementaryAbelian p E → Nat.card E = p ^ 4 →
          ∃ P : Subgroup ↥X,
            P ≤ E.comap (centerQuotientMap ↥X) ∧ IsPGroup p P ∧
            (∀ P' : Subgroup ↥X, P' ≤ E.comap (centerQuotientMap ↥X) → IsPGroup p P' →
              P' ≤ P) ∧
            P.map (centerQuotientMap ↥X) = E ∧ P ⊓ Subgroup.center ↥X = centerPCore p ↥X ∧
            P ≤ Subgroup.normalizer (T : Set ↥X) ∧
            (Subgroup.normalizer (T : Set ↥X)).map X.subtype ≤
              Subgroup.normalizer ((T.map X.subtype : Subgroup H) : Set H) ∧
            CFSG.pRank p ↥P = 3 ∧ centerPCore p ↥X ≠ ⊥ ∧ p ∣ Nat.card (Subgroup.center ↥X) ∧
            ∃ d : ℕ, Nat.card {a : ↥P // a ∈ (centerPCore p ↥X).subgroupOf P ∧ a ^ p = 1} =
                p ^ d ∧ (d = 1 ∨ d = 2) ∧
              ∃ _ : ((centerPCore p ↥X).subgroupOf P).Normal,
                CentralOddExtensionExactlyOneCase ((centerPCore p ↥X).subgroupOf P) p d) ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      (3 < localRank p (↥X ⧸ Subgroup.center ↥X) ↔
        ∃ U : Subgroup (↥X ⧸ Subgroup.center ↥X), IsPGroup 2 U ∧ U ≠ ⊥ ∧
          ∃ E : Subgroup (↥X ⧸ Subgroup.center ↥X),
            E ≤ Subgroup.normalizer (U : Set (↥X ⧸ Subgroup.center ↥X)) ∧
            IsElementaryAbelian p E ∧ Nat.card E = p ^ 4)

end CFSG.RankThree.PartOne
