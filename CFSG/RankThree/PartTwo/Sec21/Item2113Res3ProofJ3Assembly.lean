module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3KSylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem item217InLLocal_of_res3
    (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (hI : Item217InLIrredCover) (hT : Item217InLTransCover)
    (hKA : KS217J3CoverPreimage) (hKB : KS217J3CoverNoTransvection)
    (hKC : KS217J3CoverSylowFix) : Item217InLLocal :=
  Item2113Proof.item217InLLocal_of (item217InLIrred_of hI) (item217InLTrans_of hT)
    (item217InLSylow_of_kfacts h45 h66 hKA hKC) (item217InLNoTrans_of_kfacts h45 h66 hKA hKB)

theorem item217_of_res3
    (hMcL : KFacts.KP14.SylowTransvectionGL43) (h211 : Item211)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hI : Item217InLIrredCover)
    (hT : Item217InLTransCover) (hKA : KS217J3CoverPreimage)
    (hKB : KS217J3CoverNoTransvection) (hKC : KS217J3CoverSylowFix)
    (hOut : Item217NotInLLocal) : Item217 :=
  item217_of_items hMcL h211 (item217InLLocal_of_res3 h45 h66 hI hT hKA hKB hKC) hOut

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
