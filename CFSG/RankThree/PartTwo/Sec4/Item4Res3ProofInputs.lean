module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec4.Item413Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Props

@[expose] def Inputs413L2Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    ∀ e : ℕ, 1 ≤ e →
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 e)) →
      ∃ x ∈ E, ∃ m : ℕ, 2 < m ∧ Nonempty (L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        InducesStdKind L x .field

@[expose] def Inputs413L3Nine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 3 2)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 3 2) → False

@[expose] def Inputs413CoverU43McL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G), Hyp413 L A E c →
    (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 ∧
        Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸
          Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃* projSU 4 3 1)) ∨
      IsExtOf (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.McL
        (Multiplicative (ZMod 3)) →
    A ≤ L ∧ ∃ (K : Subgroup L) (_ : K.Normal), K.map L.subtype = Subgroup.zpowers c ∧
      (Nonempty (L ⧸ K ≃* projSU 4 3 1) ∨ Nonempty (L ⧸ K ≃* Blueprint.NativeSporadic.McL))

end Props

end CFSG.RankThree.PartTwo.Sec4
