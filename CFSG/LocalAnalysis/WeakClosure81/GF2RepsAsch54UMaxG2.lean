module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def Asch80G2Prime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (E T : Subgroup Y) (r : ℕ), E.Normal → r.Prime → r ≠ 2 →
    LieModel ↥E .G2 0 r 1 → Subgroup.centralizer (E : Set Y) = ⊥ → IsSylowIn 2 T ⊤ →
    ¬ HasUniqueMaxOver T

end CFSG.LocalAnalysis.WeakClosure81

end
