module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutElem
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJRefine
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutMain

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

section Assembly


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem item217NotInLLocal_of_J (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h211 : Item211) (h212 : Item212) (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hJ : Sec217OutJ) : Item217NotInLLocal :=
  item217NotInLLocal_of_steps h45 h48
    (sec217OutSecond_of h45 h48 h211 h212 h213 h214 h215 hGA) (sec217OutElements_of h45)
    (sec217OutTransvection_of h45) (sec217OutJCentral_of h45 hJ)

end Assembly

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
