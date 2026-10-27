module

public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def D321Spelled : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) →
      orbSup T V = ⊤ ∨
        (IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤ ∧
          commV L ≤ fixV (conjAutSub t L) ∧ (D321Two L ∨ D321Three Mp L))

@[expose] def D321O2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) →
      Mp = L ⊔ conjAutSub t L → qhatOf M ≤ ((2 : ℚ) : WithTop ℚ) → orbSup T V ≠ ⊤ →
      IsPSL 3 2 1 ↥L →
      Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 5 ∨
        (Nat.card ↥(oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)))) = 25 ∧
          ∀ x ∈ oTwoUpper (M ⊓ Subgroup.centralizer (Mp : Set (MulAut W))), x ^ 5 = 1)

end CFSG.Quasithin.H13.T326
