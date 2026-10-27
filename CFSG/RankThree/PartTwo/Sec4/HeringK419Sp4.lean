module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofAutThree
public import CFSG.RankThree.PartTwo.Sec4.HeringK419SympModel
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSp)
open Item419Res3 HeringK419

theorem k419AutThreeInnerSp4_holds : K419AutThreeInnerSp4 := by
  intro n hn k hk3 hk1
  have hn0 : n ≠ 0 := by omega
  refine hasTwoWitness_of_mulEquiv (Res417Six.projSpEquivSp (GaloisField 2 n)) ?_
  exact hasTwoWitness_statedSp le_rfl (by rw [← map_pow, hk3, map_one])
    (fun h => hk1 (EmbeddingLike.map_eq_one_iff.mp h))

end CFSG.RankThree.PartTwo.Sec4
