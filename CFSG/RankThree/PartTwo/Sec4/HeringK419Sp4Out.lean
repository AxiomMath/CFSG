module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
public import CFSG.RankThree.PartTwo.Sec4.HeringK419SympOuter
import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedSp)
open Item419Res3 HeringK419

theorem k419AutThreeOuterSp4_holds : K419AutThreeOuterSp4 := by
  intro n hn β hβ3 hβ
  have hn0 : n ≠ 0 := by omega
  haveI : Finite (GaloisField 2 n) := inferInstance
  exact exists_two_subgroup_outer
    (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp 2 (GaloisField 2 n)))
    β hβ3 hβ

end CFSG.RankThree.PartTwo.Sec4
