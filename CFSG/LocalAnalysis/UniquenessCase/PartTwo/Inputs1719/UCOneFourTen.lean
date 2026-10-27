module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def UC1_4_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M L R : Subgroup G) (n : ℕ),
    CFSG.Open.IsKGroup ↥H → S17.eM H ≤ 3 → M ≤ H → L ∈ calC M → Fstar L = pCoreOf 2 L →
      IsSz (Bar2 L) n → CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 M L) →
      H ⊓ normalizer (R : Set G) ≤ M →
      (∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
        H ⊓ normalizer (A : Set G) ≤ M) →
      L ∈ calC H

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
