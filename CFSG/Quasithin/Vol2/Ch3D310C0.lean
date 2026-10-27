module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D310C0 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → Mp = L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → fixV L = ⊥ →
      (∀ t ∈ T, t ∈ stabSub V) ∨ D310Two T L V

end CFSG.Quasithin
