module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.Timmesfeld

@[expose] def OddTranspRootL2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (D : Set K), Bridge.Asc72.Setup K D → pCore 2 K = ⊥ →
    Subgroup.center K = ⊥ → (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    ¬ Connectivity.Disconnected D → ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x →
      IsL2Gen (Subgroup.closure (rootSet D d)) (Subgroup.closure (rootSet D x))

end CFSG.RankThree.GF2n.Tim81
