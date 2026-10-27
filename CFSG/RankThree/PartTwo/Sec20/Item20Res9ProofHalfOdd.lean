module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms

namespace Res9

variable {F : Type} [Field F]

theorem le_of_isPGroup_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {N P : Subgroup G} [N.Normal] (hN : ¬ p ∣ N.index) (hP : IsPGroup p P) :
    P ≤ N := by
  have hQ : IsPGroup p (P.map (QuotientGroup.mk' N)) := hP.map _
  have hdvd : Nat.card (P.map (QuotientGroup.mk' N)) ∣ N.index :=
    Subgroup.card_subgroup_dvd_card _
  have h1 : Nat.card (P.map (QuotientGroup.mk' N)) = 1 := by
    rcases hQ.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (h.trans hdvd) hN
  rw [Subgroup.card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

end Res9

end CFSG.RankThree.PartTwo.Sec20
