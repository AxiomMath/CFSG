module

public import CFSG.RankThree.PartTwo.Sec10.Notation
public import CFSG.RankThree.PartTwo.Sec9.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Sec10Never : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), ¬ Sec10Std G A c L a R

@[expose] def Item1016 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec9.Hyp91 G A c L a R →
      Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)

theorem item1016_of_item96 (h96 : Sec9.Item96) (h10 : Sec10Never) : Item1016 := by
  intro G _ _ A c L a R h
  rcases h96 G A c L a R h with h27 | hl
  · exact absurd ⟨h, h27⟩ (h10 G A c L a R)
  · exact hl

end CFSG.RankThree.PartTwo.Sec10
