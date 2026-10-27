module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2_involution_product : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal → IsSpor ↥K .J2 →
    ∀ a : Y, a * a = 1 → (∃ k ∈ K, a * k ≠ k * a) →
      ∃ y ∈ K, orderOf (a * (y⁻¹ * a * y)) = 4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
