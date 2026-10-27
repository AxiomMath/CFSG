module

public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.RankThree.GF2n.Stroth80.Ctx

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def OddCentralLiftStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (Zc : Subgroup K) [Zc.Normal], Zc ≤ Subgroup.center K →
    Odd (Nat.card Zc) → ∀ T : Subgroup K, IsPGroup 2 T →
    (ConjTwoTransitive (K ⧸ Zc) (T.map (QuotientGroup.mk' Zc)) → ConjTwoTransitive K T) ∧
    ((∀ x : K ⧸ Zc, conjSubgroup x (T.map (QuotientGroup.mk' Zc)) ⊓
        Subgroup.normalizer ((T.map (QuotientGroup.mk' Zc) : Subgroup (K ⧸ Zc)) :
          Set (K ⧸ Zc)) ≠ ⊥) →
      ∀ k : K, conjSubgroup k T ⊓ Subgroup.normalizer (T : Set K) ≠ ⊥)

@[expose] def NormalLiftStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal] (T : Subgroup X), T ≤ K →
    IsPGroup 2 T →
    (∀ g : X, conjSubgroup g T ≤ Subgroup.normalizer (T : Set X) → conjSubgroup g T = T) →
    (ConjTwoTransitive K (T.subgroupOf K) → ConjTwoTransitive X T) ∧
    ((∀ k : K, conjSubgroup k (T.subgroupOf K) ⊓
        Subgroup.normalizer ((T.subgroupOf K : Subgroup K) : Set K) ≠ ⊥) →
      ∀ x : X, conjSubgroup x T ⊓ Subgroup.normalizer (T : Set X) ≠ ⊥)

@[expose] def Form2DichotomyStatement : Prop :=
  CFSG.LargeExtraspecial.S4.Form2StrongStmt →
    ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsWC L →
    (∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) →
    (∀ x : X, conjSubgroup x L ≤ Subgroup.normalizer (L : Set X) → conjSubgroup x L = L) →
    16 ≤ Nat.card L →
    ConjTwoTransitive X L ∨
      (∀ x : X, conjSubgroup x L ⊓ Subgroup.normalizer (L : Set X) ≠ ⊥) ∨
      (Nat.card L = 16 ∧ 11 ∣ Nat.card (Subgroup.normalClosure (L : Set X)))

@[expose] def Eleven37Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (_hc : Ctx M Q Z B), Width Q Z 3 → Nat.card Z = 4 →
    ¬ 11 ∣ Nat.card (bar M Q (Lgen M (LB M Q B)))

end CFSG.RankThree.GF2n.Stroth80.Tim37
