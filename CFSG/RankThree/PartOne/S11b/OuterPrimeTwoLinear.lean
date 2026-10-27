module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoGeneral
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
import CFSG.RankThree.GroupTheory.SteinbergBMVanishingFullPerfectSupplement
import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived

theorem statedClassicalModel_centerQuotient {S : Type} [Group S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : StatedClassicalModel S t n p f) :
    StatedClassicalModel (S ⧸ Subgroup.center S) t n p f := by
  have hcenter : Subgroup.center S = ⊥ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.center_eq_bot_of_isSimpleGroup hnonab
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm h

theorem outerPrimeTwoTrivial_linear {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} (h : StatedClassicalModel S .PSL n p f) :
    OuterPrimeTwoTrivial S := by
  have hperf : Group.IsPerfect S :=
    CFSG.RankThree.GroupTheory.SteinbergBM.isPerfect_of_isSimpleGroup_of_noncomm hnonab
  obtain ⟨-, -, ⟨N, hN, hcyc, -, hab⟩, -⟩ :=
    linear_perfect_cover_outer_derived_diagonal_bound S n p f
      (statedClassicalModel_centerQuotient hnonab h)
  have := hN
  have := hcyc
  exact outerPrimeTwoTrivial_of_cyclic_abelian_quotient N hab

theorem outerPrimeTwoTrivial_unitary {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} (h : StatedClassicalModel S .PSU n p f) :
    OuterPrimeTwoTrivial S := by
  have hperf : Group.IsPerfect S :=
    CFSG.RankThree.GroupTheory.SteinbergBM.isPerfect_of_isSimpleGroup_of_noncomm hnonab
  obtain ⟨-, -, N, hN, hcyc, -, hab⟩ :=
    unitary_perfect_cover_outer_derived_diagonal_bound S n p f
      (statedClassicalModel_centerQuotient hnonab h)
  have := hN
  have := hcyc
  exact outerPrimeTwoTrivial_of_cyclic_abelian_quotient N hab

end CFSG.RankThree.PartOne
