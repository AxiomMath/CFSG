module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Inner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowHNTh

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Rows


theorem rowOfH2_hn : RowOfH2 (Spor .HN) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .HN ≃* Spor .HN) :=
    CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .HN)) := by
    rw [CFSG.RankThree.PartOne.SPOR.card_outer_HN]
    norm_num
  exact rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) good425_spor_HN

theorem rowOfH2_th : RowOfH2 (Spor .Th) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Th ≃* Spor .Th) :=
    CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
      CFSG.RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  exact rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) good425_spor_Th

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
