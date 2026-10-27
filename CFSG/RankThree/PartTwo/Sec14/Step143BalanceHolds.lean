module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1NoSuz
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec14

theorem step143Balance_holds
    : Step143Balance := by
  obtain ⟨h45, -, h41, -, -, -, -, -, -, -, -⟩ := Ronan148M.closedInputs
  exact step143Balance_of h45 KFacts.kpSz
    (step143BalanceSz_of_comp2 (Ronan148K.ks143LBalComp2_of_open h41
      Ronan148K.k143OpenChar2_holds.toLie.toNoSuz.toK143Open))

end CFSG.RankThree.PartTwo.Sec14
