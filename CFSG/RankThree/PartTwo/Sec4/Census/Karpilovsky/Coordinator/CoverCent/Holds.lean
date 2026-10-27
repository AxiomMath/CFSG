module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.CoverCentRows
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4


theorem k424CoverCent_of_alt_ON (hA6 : NoType424At3 (alternatingGroup (Fin 6)))
    (hA7 : NoType424At3 (alternatingGroup (Fin 7)))
    (hON : NoType424At3 (Blueprint.NativeSporadic.Carrier .ONan)) : K424CoverCent :=
  CFSG.AGLEmbeddingD2.Wilson.Census424Cover.k424CoverCent_of_coverCentX
    (coverCentX_of_rows hA6 hA7 Proving.noType424At3_M22 ComponentPrimary.noType424At3_J3
      UniversalCoverMonster.noType424At3_McL hON
      (fun _ _ hS => UniversalCoverMonster.noType424At3_G2 hS)
      UniversalCoverMonster.noType424At3_U43)


theorem k424CoverCent_holds : K424CoverCent :=
  k424CoverCent_of_alt_ON (Proving.noType424At3_alt (by norm_num))
    (Proving.noType424At3_alt (by norm_num)) ComponentPrimary.noType424At3_ON

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
