module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Inner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowSuzLy

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Rows


theorem rowOfH2_suz : RowOfH2 (Spor .Suz) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Suz ≃* Spor .Suz) :=
    CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Suz) :=
    Finite.of_equiv _ CFSG.Sporadic.SuzOddCore.suzEquivM.symm.toEquiv
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) := by
    rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
    norm_num
  have hall : ∀ s : Blueprint.NativeSporadic.Carrier .Suz, orderOf s = 3 →
      Good425 (Subgroup.centralizer ({s} : Set (Blueprint.NativeSporadic.Carrier .Suz))) :=
    good425_all_of_subgroupModel CFSG.Sporadic.SuzOddCore.suzEquivM good425_suz
  refine rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) ?_
  intro S _ _ _ _ ⟨e⟩ s hs
  exact good425_centralizer_of_mulEquiv (e.trans b.symm)
    (hall _ (by rw [MulEquiv.orderOf_eq]; exact hs))

theorem rowOfH2_ly : RowOfH2 (Spor .Ly) := by
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃* Spor .Ly) :=
    CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Ly)) := by
    rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num
  refine rowOfH2_of_good425
    (cubeInner_of_mulEquiv b.symm (cubeInner_of_not_three_dvd_card_outer hout)) ?_
  intro S _ _ _ _ ⟨e⟩ s hs
  exact good425_centralizer_of_mulEquiv (e.trans b.symm)
    (good425_ly _ (by rw [MulEquiv.orderOf_eq]; exact hs))

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
