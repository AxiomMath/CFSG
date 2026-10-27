module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporThCent
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census th_orderOf)

theorem listRow_thJ :
    ListRow ↥CFSG.Sporadic.Th.J := by
  haveI : Finite ↥CFSG.Sporadic.Th.J :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨hoS, hoZ, hoU⟩ := th_orderOf
  exact listRow_of_three_classes (a := thS) (b := thZ) (c := thU) (fun s hs => th_census s hs)
    hoS hoZ hoU th_three_dvd_index_S th_witness_Z th_three_dvd_index_U

theorem listRow_th :
    ListRow NativeSporadic.Th := by
  haveI : Finite NativeSporadic.Th :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  exact ListRow.of_mulEquiv (S := ↥CFSG.Sporadic.Th.J) (T := NativeSporadic.Th)
    CFSG.Sporadic.Th.thEquivJ.symm listRow_thJ

theorem outerRow_th :
    OuterRow NativeSporadic.Th := by
  haveI : Finite NativeSporadic.Th :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  refine outerRow_of_not_three_dvd_outer ?_
  have h1 : Nat.card (Outer NativeSporadic.Th) = 1 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Th_native
  rw [h1]
  norm_num

theorem row_carrier_th :
    RowOf (NativeSporadic.Carrier .Th) := by
  haveI : Finite NativeSporadic.Th :=
    Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
  intro S _ _ _ _ ⟨e⟩
  exact GoodRow.of_mulEquiv (S := NativeSporadic.Th) e.symm ⟨listRow_th, outerRow_th⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
