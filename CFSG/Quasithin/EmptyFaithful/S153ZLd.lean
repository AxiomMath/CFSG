module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D391L : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    Mp = L → D3Std M Mp T L V → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
    (V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) →
    ∀ A : Subgroup (MulAut W), IsA2 M A → A ≤ T → commSeries A 3 = ⊥ → rAV A ≤ 2 →
      (∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) →
      orbSup T V = ⊤ ∨ (V = orbSup T V ∧ IsFFModule (autSec (L ⊔ T) V (fixV Mp)))

end CFSG.Quasithin
