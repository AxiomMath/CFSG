module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsL35
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsL317
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsU37
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsU331
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3WordsU3127

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem asc82Item1412L3_holds :
    Asc82Item1412L3 :=
  asc82Item1412L3_of_inputs
    (fun _ _ _ _ _ hC _ _ hL _ hbL hb2 _ hyL hy3 => gen_normalizer_omega1412 hC hL hbL hb2 hyL hy3)
    (haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩; fun β hβ => excl1412_L3_5 β hβ)
    (haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩; fun β hβ => excl1412_L3_17 β hβ)
    (fun K _ h α hα => excl1412_U3_7 K h α hα) (fun K _ h α hα => excl1412_U3_31 K h α hα)
    (fun K _ h α hα => excl1412_U3_127 K h α hα)

end CFSG.RankThree.PartTwo.Sec20
