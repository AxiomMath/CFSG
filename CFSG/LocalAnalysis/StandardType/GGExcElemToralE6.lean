module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Steinberg
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType

open CFSG.StandardType.ExcElemToral CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem ggE6ElemToralFiveInput_holds : GGE6ElemToralFiveInput := by
  intro K _ _ _ hpq s hs
  exact ggExcToral_zpowers_of_monomialToral Nat.prime_five
    monomialToralAt_E6_five
    (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E6_five a ha).le)
    hpq (fun a ha => TableBExc.fullp_E6 (by norm_num) (by norm_num) a ha) hs

end CFSG.StandardType
