module

public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec10.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item1134 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoF G → A ∉ partTwoT G → c ∈ A → c ≠ 1 → L ∈ lStarAt A c →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    ((∃ E ∈ partTwoE G, E ≤ A ∧ Sec8.InvTwoBarNontrivial E L) ∨
      (Nat.card A = 27 ∧ ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
        ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
          Sec4.thetaQuotCentralizer L)) →
    (Nat.card A = 27 → partTwoE G = partTwoF G) →
    ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

@[expose] def Item1134E27 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    PartTwoStanding G → A ∈ partTwoF G → A ∉ partTwoT G → Nat.card A = 27 → c ∈ A → c ≠ 1 →
    L ∈ lStarAt A c →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) →
    ((∃ E ∈ partTwoE G, E ≤ A ∧ Sec8.InvTwoBarNontrivial E L) ∨
      (Nat.card A = 27 ∧ ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
        ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
          Sec4.thetaQuotCentralizer L)) →
    (Nat.card A = 27 → partTwoE G = partTwoF G) →
    ∀ x ∈ A, ¬ KFacts.InducesStdKind L x .field ∧ ¬ KFacts.InducesStdKind L x .graphField

@[expose] def Sec11Never : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), ¬ Sec11Std G A c L a R Y

@[expose] def Hyp91Never : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), ¬ Sec9.Hyp91 G A c L a R

@[expose] def SetUp11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec9.Hyp91 G A c L a R → Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L) →
      ∃ Y ∈ thetaComponentsAt 3 a, sec11K L a ≤ Y

theorem hyp91Never_of_item1016 (h1016 : Sec10.Item1016) (hY : SetUp11) (h11 : Sec11Never) :
    Hyp91Never := by
  intro G _ _ A c L a R h
  have hl := h1016 G A c L a R h
  obtain ⟨Y, hY, hKY⟩ := hY G A c L a R h hl
  exact h11 G A c L a R Y ⟨h, hl, hY, hKY⟩

end CFSG.RankThree.PartTwo.Sec11
