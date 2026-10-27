module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

@[expose] def LowTwoRankSectionFor (P : CFSGIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    ∀ (H : Subgroup L) (M : Type) [Group M] [Finite M], CFSG.IsQuasisimple M → ∀ π : H →* M,
      Function.Surjective π →
      (¬ ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)) →
      (∃ i : CFSGIndex, P i ∧ Nonempty ((M ⧸ center M) ≃* i.Group)) →
        CFSG.Assembly.evenRank (M ⧸ center M) ≤ 3 ∧
          ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → ¬ ℓ ∣ Nat.card (center M)

end CFSG.RankThree.PartOne.N143
