module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBCheck
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.InjectiveTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.Blueprint CFSG.AGLEmbedding

theorem kernelTrivialAt_three_B_of_fi23_cell
    (h : KernelTrivialAt (NativeSporadic.Carrier .Fi23) 3) :
    KernelTrivialAt (NativeSporadic.Carrier .B) 3 := by
  obtain ⟨f, hf⟩ := Fi23InB.exists_injective_fi23_carrier_B
  exact Proving.kernelTrivialAt_three_B_of_fi23 f hf h

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
