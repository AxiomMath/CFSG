module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Certs

@[expose] def Alt413Fix {G : Type} [Group G] [Finite G] (L A E : Subgroup G) (c : G) : Prop :=
  Alt413 L A E c ∨
    (aschbacherSolvableCore 3 L = ⊥ ∧ (Subgroup.center L).map L.subtype = Subgroup.zpowers c ∧
      Blueprint.ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 3 1 ∧
      ∀ a ∈ A, ∃ l ∈ L, ∀ y ∈ L, a * y * a⁻¹ = l * y * l⁻¹)

@[expose] def Item4_13_forwardFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ L : Subgroup G, IsComponent L →
    ∀ (A E : Subgroup G) (c : G), IsTriple413 L A E c → 4 < CFSG.Open.pRank 3 A →
      Alt413Fix L A E c

end Certs

end CFSG.RankThree.PartTwo.Sec4
