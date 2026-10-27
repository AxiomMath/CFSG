module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Chev2StarGen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Kb Eb Tb M : Subgroup Y) (r : ℕ), Kb.Normal →
    IsSimpleGroup ↥Kb → IsChev ↥Kb 2 → centralizer (Kb : Set Y) = ⊥ →
    IsSylowOf 2 Tb ⊤ → r.Prime → 7 ≤ r → r ≠ 13 → (∀ k : ℕ, r ≠ 2 ^ k + 1) →
    Nat.card Eb = r → Permutes Eb Tb → Tb ⊓ Kb ≤ M → Eb ≤ M →
    (∀ y ∈ Kb ⊔ Eb, (∀ x ∈ Eb, y⁻¹ * x * y ∈ M) → y ∈ M) → Kb ≤ M

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
