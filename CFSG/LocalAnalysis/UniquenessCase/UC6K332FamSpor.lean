module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM11
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM12
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM22
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM23
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporM24
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporJ2
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporHS
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporHe
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporRu
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporJ4
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporJ3
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporON
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowAlt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem isSimpleGroup_of_isAlt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n) (h : UC22.IsAlt X n) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact e.isSimpleGroup_congr.mpr inferInstance

theorem goodRow_of_isAlt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (h : UC22.IsAlt S n) : GoodRow S := by
  obtain ⟨e⟩ := h
  exact GoodRow.of_mulEquiv e.symm (goodRow_alternatingGroup hn)

theorem goodRow_of_isSpor
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {s : TauCeti.SporadicName}
    (hsp : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨
      s = .Ru ∨ s = .J4 ∨ s = .J3 ∨ s = .ONan) (h : UC22.IsSpor S s) : GoodRow S := by
  rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_carrier_m11 S hs hna h
  · exact row_carrier_m12 S hs hna h
  · exact row_carrier_m22 S hs hna h
  · exact row_carrier_m23 S hs hna h
  · exact row_carrier_m24 S hs hna h
  · exact row_carrier_j2 S hs hna h
  · exact row_carrier_hs S hs hna h
  · exact rowOf_of_listRowOf listRowOf_he outerRowOf_he S hs hna h
  · exact row_carrier_ru S hs hna h
  · exact row_carrier_j4 S hs hna h
  · exact row_carrier_j3 S hs hna h
  · exact row_carrier_on S hs hna h

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
