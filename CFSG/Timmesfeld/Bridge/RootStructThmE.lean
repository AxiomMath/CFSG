module

public import CFSG.Timmesfeld.Bridge.RootStructThmC

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

@[expose] def ThreeLines (D : Set G) : Prop :=
  ∃ b ∈ D, ∃ c₁ ∈ D, ∃ c₂ ∈ D, ∃ c₃ ∈ D,
    (∀ c ∈ ({c₁, c₂, c₃} : Set G), Commute b c ∧ b * c ∈ D ∧ c ∉ rootSet D b) ∧
    c₂ ∉ rootGroup D b ⊔ rootGroup D c₁ ∧ c₃ ∉ rootGroup D b ⊔ rootGroup D c₁ ∧
    c₃ ∉ rootGroup D b ⊔ rootGroup D c₂

@[expose] def ThinManyStepE : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D →
    Moufang.ExcCollConnected D → ThreeLines D → ThinOneOpposite D

@[expose] def ThinTwoStepE : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D →
    Moufang.ExcCollConnected D → ¬ ThreeLines D → ThinOneOpposite D

theorem thinOneOppositeStepE_of_split (h1 : ThinManyStepE) (h2 : ThinTwoStepE) :
    ThinOneOppositeStepE := fun G _ D hH IH hl hc hs hconn => by
  by_cases h3 : ThreeLines D
  · exact h1 G D hH IH hl hc hs hconn h3
  · exact h2 G D hH IH hl hc hs hconn h3

end CFSG.Timmesfeld.Bridge
