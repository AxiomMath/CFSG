module

public import CFSG.Timmesfeld.RootInduction
public import CFSG.Timmesfeld.Exceptional.Polar
public import CFSG.Timmesfeld.Exceptional.Residual

public section

namespace CFSG.Timmesfeld.Moufang

@[expose] def ExceptionalLeviStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    NoLevi D

@[expose] def ExceptionalNoLeviPlaneStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    NoLevi D → ExcNoPlane D

end CFSG.Timmesfeld.Moufang
