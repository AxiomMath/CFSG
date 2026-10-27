module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4RankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4SubDefs

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan48Two (_ : FanTree Γ G) : Prop :=
  ∀ T : Track Γ G, InPiStar T → ∀ a b : ℤ, IsTArc T a b → ∃ H : Subgroup G,
    SubgraphProp T a b H ∧ (∀ h ∈ H, ∀ z ∈ T.fixer, h * z * h⁻¹ ∈ T.fixer) ∧
      ∀ x ∈ Subgroup.normalizer (omega1 T.fixer : Set G) ⊓
        MulAction.stabilizer G (T.line.vert a), orderOf x = 3 → ∀ z ∈ T.fixer, x * z = z * x

end CFSG.Quasithin.Fan86
