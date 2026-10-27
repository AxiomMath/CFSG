module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint

@[expose] def D38 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → (∃ n : ℕ, SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) →
      qhatOf (autSub (Mp ⊔ T) (orbSup T V)) = ((2 : ℚ) : WithTop ℚ)

@[expose] def D38Top : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
    D3Std M Mp T L V → orbSup T V = ⊤ →
      (∃ n : ℕ, SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n) →
      qhatOf (autSub (Mp ⊔ T) (orbSup T V)) = ((2 : ℚ) : WithTop ℚ)

end CFSG.Quasithin
