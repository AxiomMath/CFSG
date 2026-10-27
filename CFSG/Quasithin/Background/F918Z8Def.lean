module

public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D321Core : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (A : Subgroup (MulAut W)),
    D3Std M Mp T L V → t ∈ T → t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
    Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → QOff Mp T A (orbSup T V) →
    (∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) → V < orbSup T V → commSub (orbSup T V) L = V →
    qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) →
    orbSup T V ≠ ⊤ → D321Two L ∨ D321Three Mp L

@[expose] def D321Concl {W : Type} [CommGroup W] (Mp L : Subgroup (MulAut W)) (t : MulAut W) :
    Prop :=
  IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
    commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L)

end CFSG.Quasithin
