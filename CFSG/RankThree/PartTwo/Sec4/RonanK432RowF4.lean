module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Refine
public import Certificates.Certificate428003

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.RankThreeEven (f4TwoIndex)

set_option linter.unusedSectionVars false

section Row


theorem listRowOf_f4_two_of_cert : ListRowOf (TauCeti.CFSGIndex.lie f4TwoIndex).Group := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := Item434F42.exists_model e
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  haveI : Finite (adjointGroup ReeTag.F4.tag K) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have hall := Certificates.certificate428003 K hK
  exact ListRow.of_mulEquiv φ.symm (listRow_of_wit3 hall)

end Row

end CFSG.RankThree.PartTwo.Sec4.RonanK432
