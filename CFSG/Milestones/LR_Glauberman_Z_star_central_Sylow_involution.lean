module

public import CFSG.Adapters.Involutions

public section

universe u v w

namespace CFSG.ZStar

theorem _root_.CFSG.Milestones.glauberman_zStar (G : Type) [Group G] [Fintype G]
    (t : G) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ N : Subgroup G, N.Normal ∧ Odd (Nat.card N) ∧
      ∀ g : G, g * t * g⁻¹ * t⁻¹ ∈ N :=
  _root_.CFSG.ZStar.glauberman_zStar G t ht1 ht2 hisolated

end CFSG.ZStar

namespace CFSG.Adapters

open CFSG in
theorem _root_.CFSG.Milestones.glauberman_zStar_central_sylow_involution {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (z : (S : Subgroup G)) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz : orderOf z = 2)
    (hwc : ∀ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) → g⁻¹ * (z : G) * g = z) :
    (∀ g : G, ∃ c ∈ Subgroup.centralizer ({(z : G)} : Set G), ∃ k ∈ oddCore G, g = c * k) ∧
      (QuotientGroup.mk (z : G) : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) :=
  _root_.CFSG.Adapters.glauberman_zStar S z hzZ hz hwc

end CFSG.Adapters
