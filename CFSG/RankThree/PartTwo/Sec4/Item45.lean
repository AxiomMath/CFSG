module

public import CFSG.RankThree.ThetaFree.Root
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartOne
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Assembly.RankThreeEven (localRank)

theorem sqtkKGroup_of_isKGroup {G : Type} [Group G] (h : CFSG.IsKGroup G) :
    CFSG.Open.SQTKTauCeti.KGroup G :=
  CFSG.KCore.KGroupAllSimple.kGroupNonab h

theorem rank3II_4_5_of_bridge (hT : CFSG.QuasithinUnique.TCKGroupBridge)
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) : Item4_5 := by
  intro G _ _ hG A hA hor L hL
  have hK : SectionRank.IsKGroupCat G := hT G (sqtkKGroup_of_isKGroup hG.kGroup)
  have he : twoLocalOddRank G ≤ 3 := by
    rw [GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact hG.evenRank_le
  have hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2 := fun r hr hr3 => by
    have := hG.localRank_lt r hr hr3
    omega
  exact (ThetaFree.original_K_group_source_four_five_theta_component_normalization_of hB hM hK he
    hq hA hor).1 L hL

end CFSG.RankThree.PartTwo.Sec4
