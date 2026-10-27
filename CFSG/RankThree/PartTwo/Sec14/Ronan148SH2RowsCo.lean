module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Inner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowCo

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Rows


theorem rowOfH2_co2 : RowOfH2 (Spor .Co2) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Co2 ≃* Spor .Co2) :=
    CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co2)) := by
    rw [CFSG.RankThree.PartOne.SPOR.card_outer_Co2]
    norm_num
  have hall : ∀ s : ↥CFSG.Sporadic.Co2Cert.co2P, orderOf s = 3 →
      Good425 (Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Co2Cert.co2P)) :=
    good425_all_of_subgroupModel (MulEquiv.refl _) good425_co2P
  refine rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) ?_
  intro S _ _ _ _ ⟨e⟩ s hs
  exact good425_centralizer_of_mulEquiv
    (e.trans (b.symm.trans CFSG.Sporadic.Co2Cert.co2PermEquiv))
    (hall _ (by rw [MulEquiv.orderOf_eq]; exact hs))

theorem rowOfH2_co3 : RowOfH2 (Spor .Co3) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Co3 ≃* Spor .Co3) :=
    CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
      CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
    norm_num
  have hall : ∀ s : ↥CFSG.Sporadic.Schreier.Co3.co3P, orderOf s = 3 →
      Good425 (Subgroup.centralizer ({s} : Set ↥CFSG.Sporadic.Schreier.Co3.co3P)) :=
    good425_all_of_subgroupModel (MulEquiv.refl _) good425_co3P
  refine rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) ?_
  intro S _ _ _ _ ⟨e⟩ s hs
  exact good425_centralizer_of_mulEquiv
    (e.trans (b.symm.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv))
    (hall _ (by rw [MulEquiv.orderOf_eq]; exact hs))

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
