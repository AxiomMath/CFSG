module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamQ
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVU43
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowG2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Hering129C

@[expose] def KFCensus46EightChar3 : Prop :=
  KFCensusOn (fun Q _ => Nonempty (Q ≃* projSL 3 (GaloisField 3 2)) ∨
    Nonempty (Q ≃* projSU 3 3 2) ∨ Nonempty (Q ≃* projSL 4 (GaloisField 3 1)))

theorem kFCensus46Eight_of
    (h : KFCensus46EightChar3) :
    KFCensus46Eight := by
  intro Q Lb _ _ _ c a I X f hQ hD
  rcases hQ with ⟨e, he1, he2, hX⟩ | ⟨⟨φ⟩⟩ | ⟨-, hX⟩
  · have he : e = 1 ∨ e = 2 := by omega
    rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rcases he with rfl | rfl
      · exfalso
        obtain ⟨g, hg⟩ := (ppair_self hD).map φ
        have hS := RowV.card_projSL_three_char_three (e := 1) le_rfl
        exact hg.false_of_card_dvd (M := (3 ^ 1) ^ 3 * (((3 ^ 1) ^ 2 - 1) * ((3 ^ 1) ^ 3 - 1)))
          (B := 18) (by norm_num) (by norm_num) (by decide +kernel)
          ((Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hS))
      · exact h Q Lb c a I X f (Or.inl ⟨φ⟩) hD
    · rcases he with rfl | rfl
      · exfalso
        obtain ⟨g, hg⟩ := (ppair_self hD).map φ
        have hS := RowV.card_projSU_three_char_three (e := 1) le_rfl
        exact hg.false_of_card_dvd (M := (3 ^ 1) ^ 3 * (((3 ^ 1) ^ 2 - 1) * ((3 ^ 1) ^ 3 + 1)))
          (B := 19) (by norm_num) (by norm_num) (by decide +kernel)
          ((Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hS))
      · exact h Q Lb c a I X f (Or.inr (Or.inl ⟨φ⟩)) hD
  · exact h Q Lb c a I X f (Or.inr (Or.inr ⟨φ⟩)) hD
  ·
    exfalso
    obtain ⟨J, g, hg⟩ := ppair_of_census_quot hD (Subgroup.center Q) le_rfl
    rcases hX with hG | ⟨⟨φ⟩⟩
    · have hS := Sec4.RonanK432.card_of_chevalleyExceptionalModel_G2 hG
      exact hg.false_of_card_dvd (M := CFSG.Open.ordG2 (3 ^ 1)) (B := 170) (by decide)
        (by decide +kernel) (by decide +kernel)
        ((Subgroup.card_subgroup_dvd_card _).trans (dvd_of_eq hS))
    · obtain ⟨g', hg'⟩ := hg.map φ
      exact hg'.false_of_card_dvd (M := 653184) (B := 87) (by norm_num) (by norm_num)
        (by decide +kernel) (RowV.card_centralizer_u43_dvd _ hg'.orderOf_s)

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
