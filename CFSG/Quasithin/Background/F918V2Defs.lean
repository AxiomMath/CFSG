module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

structure TwoTypeBase (Λ T₀ : Subgroup Γ) (Vq : Subgroup Q) (t : Γ) : Prop where
  exp : ∀ q : Q, q ^ 2 = 1
  normal : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ
  irr : XMod.IsIrr ↥Λ Vq
  two : IsPGroup 2 ↥T₀
  gen : (⨆ g : Γ, g • Vq) = ⊤
  tT : t ∈ T₀
  stab : ∀ s ∈ T₀, s • Vq = Vq ∨ s • Vq = t • Vq
  tmove : t • Vq ≠ Vq
  noniso : ¬ XMod.Iso ↥Λ Vq (t • Vq)

structure TwoType (Λ T₀ : Subgroup Γ) (Vq : Subgroup Q) (t : Γ) : Prop extends
    TwoTypeBase Λ T₀ Vq t where
  types : ∀ g : Γ, XMod.Iso ↥Λ (g • Vq) Vq ∨ XMod.Iso ↥Λ (g • Vq) (t • Vq)

end CFSG.Quasithin.Z391
