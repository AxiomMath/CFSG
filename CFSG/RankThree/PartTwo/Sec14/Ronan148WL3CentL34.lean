module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3Cent
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentPipe
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentSinger

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4


theorem kFact148L3CentL34 : KFact148L3CentL34 := by
  intro X _ _ D E hD hED hEc hE3 hE27 ha e heED he1 heE hF3 hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, K, _, hchar, hK, hq, α, e₀, hc, -, -, -, hd⟩ := exists_centConfig_of_kfact
    (by norm_num) hD (by norm_num) hED hEc hE3 hE27 ha heED he1 heE hF3 hV
  cases π
  · change 2 ^ 2 % 3 = 2 at hq
    norm_num at hq
  rcases hd with ⟨τ, hτ, hτ1, he₀⟩ | ⟨-, -, -, -, h9⟩
  · exact hc.false_of_L34 hK hτ hτ1 he₀
  · change 2 ^ 2 % 9 = 1 at h9
    norm_num at h9

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
