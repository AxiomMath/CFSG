module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2_center_five : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    IsSpor ↥K .J2 →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ x ∈ K, orderOf x = 5 ∧
        ∀ z ∈ S, (∀ w ∈ S, z * w = w * z) → x * z = z * x

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
