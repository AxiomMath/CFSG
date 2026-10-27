module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def D10YPairExists (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ α : V, valence Γ α = 5 → ∃ (D : D10Set L α) (δ' : V), D.IsYPair δ'

end CFSG.Quasithin.Fan86
