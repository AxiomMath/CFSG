module

public import CFSG.RankThree.PartTwo.Sec9.NormalizerL
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiInndiag
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiFix
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCent

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem slPiInndiag : SLPiInndiag := fun _ _ _ _ _ hn hL =>
  KFacts.exists_inndiag_of_isSLThreePiAt hn hL

theorem slPiSylowFixed : SLPiSylowFixed := fun _ _ _ _ hn hX T _ hζ hfix =>
  KFacts.eq_one_of_forall_sylow_fixed_of_isSLThreePiAt hn hX T hζ hfix

theorem slPiFieldSylowFixed : SLPiFieldSylowFixed :=
  fun _ _ _ _ _ hn hL _ haN ha3 ha _ hT _ hζ hfix =>
    KFacts.mem_zpowers_of_forall_sylow_barCentralizer_fixed hn hL haN ha3 ha hT hζ hfix

theorem hyp92Never_of_item95 (h95 : Item95) (h45 : Sec4.Item4_5) : Hyp92Never :=
  hyp92Never_of_item45 h95 h45 slPiInndiag slPiSylowFixed slPiFieldSylowFixed

theorem item96_of_item95
    (h82 : Sec8.Item82One) (h95 : Item95) (h45 : Sec4.Item4_5) (h8 : NotLTwoEight) : Item96 :=
  item96_of_item82 h82 (hyp92Never_of_item95 h95 h45) h8

end CFSG.RankThree.PartTwo.Sec9
