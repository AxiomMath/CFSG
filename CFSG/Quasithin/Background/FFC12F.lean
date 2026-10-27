module

public import CFSG.Quasithin.Background.FFC12C
public import CFSG.Quasithin.Background.FFC12E

public section

namespace CFSG.Quasithin

namespace B69

structure AsB69DeepInputsRest : Prop where
  sp4 : AsB69NoRankTwoSp4
  a6 : AsB69NoRankTwoA6
  tripleA6 : AsB69NoRankTwoTripleA6
  g2 : AsB69NoG2
  alt : AsB69AltCase

theorem AsB69DeepInputsRest.toDeep (h : AsB69DeepInputsRest) : AsB69DeepInputs :=
  ⟨h.sp4, h.a6, h.tripleA6, h.g2, asB69RankOneSylow_proved, asB69RankOneBorel_proved, h.alt⟩

end B69

end CFSG.Quasithin
