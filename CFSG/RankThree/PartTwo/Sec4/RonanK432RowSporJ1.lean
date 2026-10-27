module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432PRank
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint

theorem listRow_j1 : ListRow NativeSporadic.J1 :=
  listRow_of_card (by rw [CFSG.Sporadic.J1.card_J1]; norm_num)
    (by rw [CFSG.Sporadic.J1.card_J1]; norm_num)

theorem outerRow_j1 :
    OuterRow NativeSporadic.J1 :=
  outerRow_of_forall_pow_three_inner fun σ _ =>
    (CFSG.Sporadic.Schreier.at_j1_schreier.2.1 σ).elim fun g hg => ⟨g, hg.symm⟩

theorem row_carrier_j1 :
    RowOf (NativeSporadic.Carrier .J1) := by
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.J1) e.symm ⟨listRow_j1, outerRow_j1⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
