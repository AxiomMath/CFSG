module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_Ru : SporadicCoprimeRank .Ru :=
  sporadicCoprimeRank_of_card_outer_le (k := 1) (by norm_num)
    (by
      rw [show Nat.card (Outer (Carrier .Ru)) = Nat.card (Outer Sporadic.RuSchreier.ruP) from
        card_outer_eq_of_mulEquiv Sporadic.RuSchreier.ruEquivP]
      exact Sporadic.RuSchreier.card_outer_ruP.le)

end CFSG.RankThree.PartOne
