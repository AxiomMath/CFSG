module

public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

@[expose] def LineTI (D : Set G) (a d : G) : Prop :=
  ∀ g ∈ D, ∀ u ∈ D, u ∈ rootGroup D a ⊔ rootGroup D d →
    g * u * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d →
    ∀ v ∈ D, v ∈ rootGroup D a ⊔ rootGroup D d → g * v * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d

@[expose] def NormalizesLine (D : Set G) (a d g : G) : Prop :=
  ∀ u ∈ rootGroup D a ⊔ rootGroup D d, g * u * g⁻¹ ∈ rootGroup D a ⊔ rootGroup D d

@[expose] def LineCentralizerEq (D : Set G) : Prop :=
  ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a → LineTI D a d →
    ∀ f ∈ D, Commute f a → Commute f d → f ∈ rootGroup D a ⊔ rootGroup D d

end CFSG.Timmesfeld.Bridge
