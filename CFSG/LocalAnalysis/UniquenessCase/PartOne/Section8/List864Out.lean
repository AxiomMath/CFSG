module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterRu
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterG2Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List863
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 IsSpor)

theorem not_three_dvd_card_outer_of_lieModel_G2_five
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 5 1) :
    ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
  rw [card_outer_of_lieModel_G2_prime (p := 5) (by norm_num) (by norm_num) (by norm_num) h]
  norm_num

theorem not_three_dvd_card_outer_of_lieModel_G2_seven
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 7 1) :
    ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
  rw [card_outer_of_lieModel_G2_prime (p := 7) (by norm_num) (by norm_num) (by norm_num) h]
  norm_num

theorem not_three_dvd_card_outer_of_lieModel_G2_seventeen
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Blueprint.LieModel (Bar2 L) .G2 0 17 1) :
    ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
  rw [card_outer_of_lieModel_G2_prime (p := 17) (by norm_num) (by norm_num) (by norm_num) h]
  norm_num

theorem not_three_dvd_card_outer_of_list863
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : List863 (Bar2 L)) :
    ¬ 3 ∣ Nat.card (Outer (Bar2 L)) := by
  unfold List863 at h
  rcases h with h | h | h | h | h
  · exact not_three_dvd_card_outer_of_isSpor_Ru h
  · exact not_three_dvd_card_outer_of_isSpor_J4 h
  · exact not_three_dvd_card_outer_of_lieModel_G2_five h
  · exact not_three_dvd_card_outer_of_lieModel_G2_seven h
  · exact not_three_dvd_card_outer_of_lieModel_G2_seventeen h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
