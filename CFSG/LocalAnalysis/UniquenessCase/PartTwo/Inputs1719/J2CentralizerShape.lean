module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2_centralizer_shape : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    IsSpor ↥K .J2 →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      Nonempty (Bar2 (Subgroup.centralizer
          (((Subgroup.center S).map S.subtype) : Set Y)) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (Bar2 (Subgroup.centralizer
          (((Subgroup.center S).map S.subtype) : Set Y)) ≃* Equiv.Perm (Fin 5))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
