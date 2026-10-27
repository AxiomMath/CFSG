module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagMovedSection
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagMovedRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


section Certs


theorem ys03_I03_moved_component {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L : Subgroup G}
    (hS : SchreierFor CFSG.Assembly.InCatalog) (h45 : Item4_5)
    (h : DiagSetting G A M H s L) (K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) (hK : CFSG.IsComponent K)
    (hmoved : ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
      Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G))) :
    HasSection (K ⧸ Subgroup.center K) (projSL 3 (GaloisField 2 2)) ∧ 1 < CFSG.Open.pRank 3 K := by
  have hsec := ys03_section_of_item45 hS h45 h K hK hmoved
  exact ⟨hsec, ys03_one_lt_pRank_of_hasSection_L34 K (ys03_center_isPGroup_of_component hK) hsec⟩

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
