module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem rowOf_spor_of_carrier {s : TauCeti.SporadicName}
    (hb : Nonempty (NativeSporadic.Carrier s ≃* Spor s)) (h : RowOf (NativeSporadic.Carrier s)) :
    RowOf (Spor s) := by
  intro S _ _ hs hna ⟨e⟩
  obtain ⟨b⟩ := hb
  exact h S hs hna ⟨e.trans b.symm⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
