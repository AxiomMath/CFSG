module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D391LLTop : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → ∀ t ∈ T,
    t ∉ Subgroup.normalizer (L : Set (MulAut W)) → Mp = L ⊔ conjAutSub t L → V = orbSup T V →
    ∀ A : Subgroup (MulAut W), QOff Mp T A (orbSup T V) → orbSup T V = ⊤

@[expose] def D391NotFFTop : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → V = orbSup T V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → ¬ IsFFModule (autSec (Mp ⊔ T) V (V ⊓ fixV Mp))

end CFSG.Quasithin
