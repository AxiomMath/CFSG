module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

@[expose] def s16c2m_FixThree {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) (J : Subgroup W) :
    Prop :=
  4 ≤ rk ↥J ∧ ∀ u ∈ J, u ≠ 1 → ∃ y ∈ L, orderOf y = 3 ∧ y u = u

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
