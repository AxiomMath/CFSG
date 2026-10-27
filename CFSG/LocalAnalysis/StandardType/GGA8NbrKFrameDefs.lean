module

public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel

public section

namespace CFSG.StandardType.A8Coord

@[expose] def GGA8KFrame {G : Type} [Group G] (Bs K : Subgroup G) (y : G) (hy : y ∈ Bs)
    (ρ : ↥K ≃* (GGSL9V ≃ₗ[ZMod 2] GGSL9V)) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)) : Prop :=
  ι (Additive.ofMul ⟨y, hy⟩) = Pi.single 0 1 ∧
    (∀ b : ↥Bs, ι (Additive.ofMul b) 0 = 0 ↔ (b : G) ∈ K) ∧
    ∀ (b : ↥Bs) (hb : (b : G) ∈ K), ρ ⟨b, hb⟩ =
      ggSL9TorusCoord (Multiplicative.ofAdd fun i : Fin 3 => ι (Additive.ofMul b) i.succ)

end CFSG.StandardType.A8Coord

end
