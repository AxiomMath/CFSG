module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3Cent
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentPipe
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentL34
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentU38

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4


theorem kFact148L3CentU38 : KFact148L3CentU38 := by
  intro X _ _ D E hD hED hEc hE3 hE27 ha e heED he1 heE hF3 hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, K, _, hchar, hK, hq, α, e₀, hc, he₀1, he₀3, hcard, hd⟩ := exists_centConfig_of_kfact
    (by norm_num) hD (by norm_num) hED hEc hE3 hE27 ha heED he1 heE hF3 hV
  cases π
  · exact hc.false_of_U38 hK he₀1 he₀3 hcard hd
  · change 2 ^ 3 % 3 = 1 at hq
    norm_num at hq

theorem kFact148L3Cent : Ronan148A.KFact148L3Cent :=
  kFact148L3Cent_of kFact148L3CentL34 kFact148L3CentU38

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
