module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E27
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LU45
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH1Five

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem rankThreeData_of_invE9 {X : Type} [Group X] (hcube : CubeInner X) (h : InvE9 X) :
    Ronan148R.RankThreeData X := by
  obtain ⟨F, F', hFF', hF, hF9, hF', t, ht1, ht2, htF⟩ := h
  exact ⟨hcube, ⟨F, F', hFF', hF, hF9, hF'.1, hF'.2, t, ht1, ht2, htF⟩⟩

section Rows


theorem kH1_four_SU_five
    : RowOf427 (projSU 4 5 1) :=
  Ronan148R.rowOf427_of_e27Move (center_eq_bot_of_noThreeCover' noThreeCover_projSU45)
    (rankThreeData_of_invE9 (cubeInner_of_not_three_dvd_card_outer
      RonanK432.not_three_dvd_card_outer_projSU_four_prime) invE9_projSU45)
    e27Move_projSU45


theorem kH1_eight_SL4
    : RowOf427 (projSL 4 (GaloisField 2 2)) :=
  Ronan148L.RowOf427.of_mulEquiv KFacts.KS21.L44.equivSL
    (Ronan148R.rowOf427_of_e27Move
      (center_eq_bot_of_noThreeCover' (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv
        KFacts.KS21.L44.equivSL.symm noThreeCover_projSL_four_four))
      (rankThreeData_of_invE9 (cubeInner_of_mulEquiv KFacts.KS21.L44.equivSL.symm
        (cubeInner_of_not_three_dvd_card_outer RonanK432.not_three_dvd_card_outer_projSL4)) invE9_M)
      e27Move_M)

theorem kH1_eight_Sp6_4
    : RowOf427 (projSp 3 (GaloisField 2 2)) :=
  Ronan148L.RowOf427.of_mulEquiv KFacts.KS21.Sp64.equivSp
    (Ronan148R.rowOf427_of_e27Move
      (center_eq_bot_of_noThreeCover' (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv
        KFacts.KS21.Sp64.equivSp.symm noThreeCover_projSp_three_four))
      (rankThreeData_of_invE9 (cubeInner_of_mulEquiv KFacts.KS21.Sp64.equivSp.symm
        (cubeInner_of_not_three_dvd_card_outer RonanK432.not_three_dvd_card_outer_projSp6))
        invE9_Sp)
      e27Move_Sp)

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
