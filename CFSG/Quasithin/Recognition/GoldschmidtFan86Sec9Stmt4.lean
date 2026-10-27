module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Amalgam
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting
public import CFSG.Quasithin.Recognition.GoldschmidtStatement

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan915 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, S.Star →
    (Nat.card ↥(MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta) = 2 ^ 11 →
      AdmitsPres 11 (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G S.α)
        (MulAction.stabilizer G S.beta))) ∧
    (Nat.card ↥(MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta) = 2 ^ 12 →
      AdmitsPres 12 (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G S.α)
        (MulAction.stabilizer G S.beta)))

end CFSG.Quasithin.Fan86
