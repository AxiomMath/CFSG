module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoBasic
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11

@[expose] def DFourThreeAKill :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (f : ℕ) (σ : K ≃+* K), 2 ≤ f →
    Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ (2 ^ f)) →
    ∀ z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, z ^ 3 = 1 → z ≠ 1 →
      ¬ PullDatum (MulAut.conj z)

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
