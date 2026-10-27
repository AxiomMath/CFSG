module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

structure N4Base (W : Type) [CommGroup W] [Finite W] (L : Subgroup (MulAut W)) (V : Subgroup W)
    (σ : MulAut W) : Prop where
  hexp : ∀ w : W, w ^ 2 = 1
  hinv : ∀ x ∈ L, ∀ v ∈ V, x v ∈ V
  hcomm : XMod.commOf ↥L V = V
  hnat : BinaryNaturalSL L V (V ⊓ fixV L) 3 1
  hZ : Nat.card ↥(V ⊓ fixV L) = 2
  hσL : ∀ x : MulAut W, x ∈ L ↔ σ * x * σ⁻¹ ∈ L
  hne : V.map σ.toMonoidHom ≠ V
  hdyn : ¬ ∃ l₀ ∈ L, ∀ x ∈ L, (σ * l₀⁻¹) * x = x * (σ * l₀⁻¹)
  hsum : V ⊔ V.map σ.toMonoidHom = ⊤
  hint : V ⊓ V.map σ.toMonoidHom ≤ fixV L

end CFSG.Quasithin
