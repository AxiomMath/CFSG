module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

@[expose] def SzAutBorelThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), IsSz e X → ∀ (S : Sylow 2 X) (α : MulAut X),
    α ^ 3 = 1 → (S : Subgroup X).map α.toMonoidHom = S →
    (∀ b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), b⁻¹ * α b ∈ (S : Subgroup X)) →
    α = 1

end CFSG.Quasithin
