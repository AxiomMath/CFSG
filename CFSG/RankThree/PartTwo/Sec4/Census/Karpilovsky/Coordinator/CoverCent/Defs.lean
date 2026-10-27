module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent

open CFSG.RankThree.PartTwo

@[expose] def NoType424At3 (S : Type) [Group S] : Prop :=
  ∀ s : S, orderOf s = 3 → ¬ Sec11.KS11Lie2Proof.HasType424 (Sec4.Item426.fixSub (MulAut.conj s))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverCent
