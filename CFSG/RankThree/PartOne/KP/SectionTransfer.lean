module

public import CFSG.RankThree.PartOne.KP.MReduction

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

@[expose] def HasSection (X Y : Type) [Group X] [Group Y] : Prop :=
  ∃ (A : Subgroup X) (N : Subgroup A) (_ : N.Normal), Nonempty ((A ⧸ N) ≃* Y)

theorem sectionsForceEvenRankFour_of_hasSection {X Y : Type} [Group X] [Group Y]
    (hY : SectionsForceEvenRankFour Y) (hXY : HasSection X Y) : SectionsForceEvenRankFour X := by
  intro G _ _ H K _ ⟨φ⟩
  obtain ⟨A, N, hN, ⟨ψ⟩⟩ := hXY
  obtain ⟨H', K', hK', ⟨χ⟩⟩ := exists_section_of_section H K φ A N ψ
  exact hY G H' K' ⟨χ⟩

theorem sectionsForceEvenRankFour_fi23_fi24prime
    (h22 : SectionsForceEvenRankFour (Carrier .Fi22))
    (h23 : HasSection (Carrier .Fi23) (Carrier .Fi22))
    (h24 : HasSection (Carrier .Fi24Prime) (Carrier .Fi23)) :
    SectionsForceEvenRankFour (Carrier .Fi23) ∧ SectionsForceEvenRankFour (Carrier .Fi24Prime) := by
  have hF23 := sectionsForceEvenRankFour_of_hasSection h22 h23
  exact ⟨hF23, sectionsForceEvenRankFour_of_hasSection hF23 h24⟩

end CFSG.RankThree.PartOne
