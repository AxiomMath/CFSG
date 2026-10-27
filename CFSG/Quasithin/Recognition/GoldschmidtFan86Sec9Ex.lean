module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def SecCfgExists (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ α β : V, valence Γ α = 5 → Γ.Adj α β →
    ∃ S : Sec9Cfg L, S.α = α ∧ S.beta = β ∧ S.Star

end CFSG.Quasithin.Fan86
