module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec11.Item116Holes

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def IsL2OddCharOne {G : Type} [Group G] (L : Subgroup G) : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField p (3 * 1)))

@[expose] def IsL3Eight {G : Type} [Group G] (L : Subgroup G) : Prop :=
  Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 3

@[expose] def IsSurvivingCase {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (∃ m : ℕ, 1 < m ∧ IsL2EvenAt L m) ∨ IsL3Eight L ∨ IsL2OddCharOne L

section Pieces


@[expose] def ResidueR1PCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d →
        inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ({a} : Set G))) ≠ ⊥

@[expose] def ResidueR1TwoStarA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L → KFAt L a → TwoStarConditionAt A a

@[expose] def ResidueR1TwoStarCD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsSurvivingCase L → KFAt L a → TwoStarConditionAt A (c * d)

@[expose] def ResidueR1TwoStarCL38 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsL3Eight L → TwoStarConditionAt A c

@[expose] def ResidueR1TwoStarCOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d : G), ResidueConfig G A c L a R Y d → A ∉ partTwoT G →
      ResidueR1 G A c a d → IsL2OddCharOne L → TwoStarConditionAt A c

end Pieces

end CFSG.RankThree.PartTwo.Sec11
