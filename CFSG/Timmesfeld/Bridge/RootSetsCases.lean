module

public import CFSG.Timmesfeld.Closure.LS

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Closure

variable {G : Type*} [Group G] {D : Set G}

@[expose] def RootFixThird (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∉ D →
    ∀ c ∈ D, ¬ Commute d c → Odd (orderOf (d * c)) → ∀ m : ℕ, Odd m →
      orderOf (c * (a * b)) ≠ 2 * m

end CFSG.Timmesfeld.Bridge
