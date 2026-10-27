module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.KernelCells
public import CFSG.RankThree.PartOne.MultRes.Trim

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.Blueprint
open CFSG.AGLEmbedding (KernelTrivialAt)

theorem bigPrimeFacts_of_ne_M (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ Nat.card (NativeSporadic.Carrier s) →
      KernelTrivialAt (NativeSporadic.Carrier s) p :=
  fun _ hp hp5 _ =>
    kernelTrivialAt_carrier_of_five_le CFSG.RankThree.PartOne.MultRes.sporadicResidualKernelsTrim_holds
      s hs hp hp5

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
