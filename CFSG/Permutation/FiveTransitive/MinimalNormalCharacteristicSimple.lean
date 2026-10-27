module

public import CFSG.Permutation.FiveTransitive.AbelianNormalObstruction
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG

namespace FiveTransitive.MinimalNormalCharacteristicSimple

theorem characteristic_eq_bot_or_top_of_minimal_normal
    (G : Type*) [Group G] (N : Subgroup G) [N.Normal]
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N)
    (H : Subgroup N) [H.Characteristic] : H = ⊥ ∨ H = ⊤ := by
  rcases hmin (H.map N.subtype) inferInstance (Subgroup.map_subtype_le H) with hbot | htop
  · exact Or.inl ((H.map_eq_bot_iff_of_injective N.subtype_injective).mp hbot)
  · right
    apply Subgroup.map_injective N.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact htop

end FiveTransitive.MinimalNormalCharacteristicSimple

end CFSG
