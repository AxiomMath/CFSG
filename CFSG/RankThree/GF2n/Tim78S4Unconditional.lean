module

public import CFSG.RankThree.GF2n.Tim78S4RootDirect
public import CFSG.RankThree.GF2n.Tim78S48Main

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

open Tim78

section Final


theorem tim78Sec4_unconditional : Tim78Sec4Statement :=
  tim78Sec4_of_rootType fun _ _ _ _ _ _ _ _ H => H.rootTypeStep_direct

end Final

end CFSG.RankThree.GF2n
