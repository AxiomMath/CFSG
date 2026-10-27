module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_J2_centralizer_fpf : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal → IsSpor ↥K .J2 →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∀ (P : Subgroup Y) (x : Y),
        P ≤ CFSG.Open.pCoreOf 2
          (Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y)) →
        x ∈ Subgroup.centralizer (((Subgroup.center S).map S.subtype) : Set Y) →
        Odd (orderOf x) → x ∈ Subgroup.normalizer (P : Set Y) →
        (∀ p ∈ P, x * p = p * x → p = 1) → P = ⊥

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
