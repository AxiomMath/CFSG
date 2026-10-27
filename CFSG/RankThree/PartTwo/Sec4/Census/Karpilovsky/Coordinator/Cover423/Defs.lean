module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423

open CFSG.RankThree.PartTwo

@[expose] def AlphaNine (S : Type) [Group S] : Prop :=
  ∀ D : Subgroup S, CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    Sec4.Res423Two.AlphaVanishes S D

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Cover423
