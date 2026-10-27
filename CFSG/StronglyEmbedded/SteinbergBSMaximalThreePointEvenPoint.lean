module

public import CFSG.StronglyEmbedded.SteinbergBUConjugateAction
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.StronglyEmbedded

open Subgroup CFSG.StronglyEmbedded.SteinbergBU

theorem two_le_pRank_two_of_commuting_involutions {X : Type*} [Group X] [Finite X] {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.pRank 2 X := by
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute hx
      hy hxy hne
  refine le_csSup ⟨Nat.card X, ?_⟩ ⟨V, hV, by rw [hVcard]; norm_num⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self one_lt_two).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card X := Subgroup.card_le_card_group B

variable {G : Type} [Group G]

end CFSG.StronglyEmbedded
