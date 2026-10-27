module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42A0Set

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Quasithin.H13

@[expose] def U42F48 : Prop :=
  ∀ (Y₀ : Type) [Group Y₀] [Finite Y₀] (β : u42Setting.α.Completion Y₀), β.IsFaithful →
    β.IsSmall (polyNumber .PSU) → u42Setting.F48Concl β

end CFSG.Quasithin.H13.F431.U42
