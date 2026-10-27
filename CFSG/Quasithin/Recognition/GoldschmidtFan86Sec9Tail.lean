module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Amalgam
public import CFSG.Quasithin.Recognition.GoldschmidtStatement

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

@[expose] def FanTailInputs : Prop :=
  ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V) (F : FanTree Γ G),
    ∃ L : ZLab Γ G, Fan7 F L ∧ Fan65 F ∧ Fan66 F ∧ Fan517 F L ∧ Fan512 F L

@[expose] def FanTail : Prop :=
  ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V) (F : FanTree Γ G) (L : ZLab Γ G),
    Fan7 F L → Fan65 F → Fan66 F → Fan517 F L → Fan512 F L →
    ∀ α β : V, Γ.Adj α β → valence Γ α = 5 →
      ∃ n : ℕ, (n = 11 ∨ n = 12) ∧
        Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ n ∧
        AdmitsPres n (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α)
          (MulAction.stabilizer G β))

end CFSG.Quasithin.Fan86
