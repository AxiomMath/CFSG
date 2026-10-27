module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2_threeCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 →
    ∀ (S : Subgroup X), CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∀ z ∈ S, (∀ w ∈ S, z * w = w * z) → orderOf z = 2 →
        ∀ Y : Subgroup X, Y ≤ Subgroup.centralizer ({(z : X)} : Set X) →
          Nat.card Y = 3 →
            ∃ P : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧
              Y = CFSG.Quasithin.centerOf P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
