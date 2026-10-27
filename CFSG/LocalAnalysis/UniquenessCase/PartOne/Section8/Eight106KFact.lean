module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KComp8106 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsKGroup Y → CFSG.Open.IsQuasisimple Y →
    Odd (Nat.card (center Y)) → CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 1 →
    ∀ n p : ℕ, 2 ≤ n → Even n → p.Prime → p ∣ 2 ^ n + 1 →
    ∀ K : Subgroup Y, ⁅K, K⁆ = K → IsL2 (Bar2 K) (2 * n) →
    IsStronglyPEmbedded p (normalizer (K : Set Y)) →
    ∀ W : Subgroup (MulAut Y), IsPGroup 2 W → (∀ α ∈ W, K.map α.toMonoidHom = K) →
      (∀ y ∈ normalizer (K : Set Y), ∀ α ∈ W, MulAut.conj y * α * (MulAut.conj y)⁻¹ ∈ W) →
      W = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
