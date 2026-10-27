module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42
public import CFSG.Quasithin.Background.A318POutHe

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (f4TwoIndex)

@[expose] def ListRowOf (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → ListRow S

@[expose] def OuterRowOf (X : Type) [Group X] : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* X) → OuterRow S

theorem rowOf_of_listRowOf {X : Type} [Group X] (hL : ListRowOf X) (hO : OuterRowOf X) :
    RowOf X :=
  fun S _ _ hs hna he => ⟨hL S hs hna he, hO S hs hna he⟩

theorem outerRowOf_f4_two : OuterRowOf (TauCeti.CFSGIndex.lie f4TwoIndex).Group := by
  intro S _ _ _ _ ⟨e⟩
  exact outerRow_of_not_three_dvd_outer (Item434F42.not_three_dvd_card_outer e)

theorem outerRowOf_tits (ht : TauCeti.LieTypeIndex.tits.Valid) :
    OuterRowOf (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  intro S _ _ _ _ ⟨e⟩
  have hm : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
    CFSG.SectionRank.reeTitsModel_of_mulEquiv e (Census.bridgeExceptional46.tits ht)
  exact outerRow_of_not_three_dvd_outer fun h3 =>
    Quasithin.A318P.not_dvd_outer_tits hm Nat.prime_three (by norm_num) h3

theorem outerRowOf_he : OuterRowOf (NativeSporadic.Carrier .He) := by
  intro S _ _ _ _ ⟨e⟩
  exact outerRow_of_not_three_dvd_outer fun h3 =>
    Quasithin.A318P.not_dvd_outer_He e Nat.prime_three (by norm_num) h3

end CFSG.RankThree.PartTwo.Sec4.RonanK432
