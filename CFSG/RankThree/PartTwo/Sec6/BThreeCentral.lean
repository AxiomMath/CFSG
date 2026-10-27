module

public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
public import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def BThreePropertyThreePrimeCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), SectionFourHyp H →
    3 ∣ Nat.card (Subgroup.center H) →
    ∀ X ∈ thetaComponentsIn H, ∀ b ∈ H, b ^ 3 = 1 → b ∈ Subgroup.normalizer (X : Set G) →
    ∀ Y : Subgroup G, Y ≤ X ⊓ Subgroup.centralizer {b} → Group.IsPerfect Y →
      (Y.subgroupOf (X ⊓ Subgroup.centralizer {b})).IsSubnormal →
      IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) → ¬ 3 ∣ Nat.card Y →
      ⁅inSubgroup (aschbacherSolvableCore 3) Y, Y⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X

theorem bThreePropertyCentral_of_lBalance (h : GWLBalanceStatement)
    (h3 : BThreePropertyThreePrimeCentral) : BThreePropertyCentral := by
  intro G _ _ H hH hZ X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq
  by_cases hY3 : 3 ∣ Nat.card Y
  · exact bThreeProperty_of_three_dvd h hH hX hbH hb3 hYXC hYp hYsn hYq hY3
  · exact h3 G H hH hZ X hX b hbH hb3 hbX Y hYXC hYp hYsn hYq hY3

theorem rank3II_6_5_of_lBalance (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hGW : GWLBalanceStatement) (h3 : BThreePropertyThreePrimeCentral) : Item6_5 :=
  rank3II_6_5_central h45 h48 h49 (bThreePropertyCentral_of_lBalance hGW h3)

theorem rank3II_6_8_of_central (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : BThreePropertyCentral) (hKf : KFacts.KS6OuterIndex) : Item6_8 :=
  rank3II_6_8 h45 (rank3II_6_6_of_central h45 h48 h49 hB3) hKf

theorem rank3II_6_8_of_lBalance (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hGW : GWLBalanceStatement) (h3 : BThreePropertyThreePrimeCentral)
    (hKf : KFacts.KS6OuterIndex) : Item6_8 :=
  rank3II_6_8_of_central h45 h48 h49 (bThreePropertyCentral_of_lBalance hGW h3) hKf

end CFSG.RankThree.PartTwo.Sec6
