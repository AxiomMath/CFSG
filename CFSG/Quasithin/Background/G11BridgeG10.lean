module

public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace G108Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem X_normalizes_H :
    ∀ x ∈ X, ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
  fun x hx h hh => normalClosure_normal Γ L x (hyp.X_le hx) h hh

end G108Hyp

end G11

end CFSG.Quasithin
