module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamCells
public import CFSG.LieType.Catalog.Realization
public import CFSG.LargeExtraspecial.A2ModOrdCard

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem isPerfect_Co1 : Group.IsPerfect NativeSporadic.Co1 := by
  have hs := CFSG.Sporadic.Co1.isSimpleGroup_Co1
  have hc := CFSG.Sporadic.Co1.card_Co1
  have hfin : Finite NativeSporadic.Co1 := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact isPerfect_of_isSimpleGroup_card_not_prime (by rw [hc]; norm_num)

theorem isPerfect_Co2 : Group.IsPerfect NativeSporadic.Co2 := by
  have hs := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  have hc := CFSG.Sporadic.Co2.card_Co2
  have hfin : Finite NativeSporadic.Co2 := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact isPerfect_of_isSimpleGroup_card_not_prime (by rw [hc]; norm_num)


theorem isPerfect_twistedE6 (X : Type) [Group X] (h : LieModel X .twistedE6 0 2 1) :
    Group.IsPerfect X := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Catalog.lieModel_finite_simple X .twistedE6 0 2 1 h
  have hc := CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_twistedE6 h
  exact isPerfect_of_isSimpleGroup_card_not_prime (by rw [hc]; norm_num [ordTwistedE6])

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
