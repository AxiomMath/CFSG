module

public import CFSG.RankThree.PartTwo.Sec11.Final1128

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem choose1128_of_final1128 (hfin : Final1128) : Choose1128 :=
  fun G _ _ A c L a R Y d x s r g a' h hsc hrs hx9 ha'A ha'cd hPP hnf =>
    (hfin G A c L a R Y d x s r g a' h hsc hrs hx9 ha'A ha'cd hPP hnf).elim

theorem item1132_of_final1128 (hfin : Final1128) : Item1132 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf => (Final1128.false_of_sec11Final hfin hf).elim

end CFSG.RankThree.PartTwo.Sec11
