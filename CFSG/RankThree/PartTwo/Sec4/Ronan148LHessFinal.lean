module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessGlue
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessSmall
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessLarge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.RankThree.PartTwo.Sec4.Ronan148B

theorem hessPhiMemClosure_holds : HessPhiMemClosure :=
  hessPhiMemClosure_of_small fun F _ p _ _ => hessPhiMemClosure_small F p

theorem kl3HessTori_holds : Sec14.KL3HessTori :=
  kl3HessTori_of_hessPhiMemClosure hessPhiMemClosure_holds

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
