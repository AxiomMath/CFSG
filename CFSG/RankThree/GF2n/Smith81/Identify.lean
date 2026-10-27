module

public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.Timmesfeld.Assembly

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem timmesfeldOutcomeStatement_of_outcome : TimmesfeldOutcomeStatement :=
  fun _ _ D h => CFSG.Timmesfeld.outcome (D := D) h

end CFSG.RankThree.GF2n.Smith81
