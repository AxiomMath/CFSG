module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.TwoPointActionCommutator

public section

namespace CFSG

namespace FiveTransitive.TwoFixedNormalizerCommutator

open MulAction

theorem fixes
    {G Y : Type*} [Group G] [MulAction G Y]
    (R : Subgroup G) [Finite (fixedPoints R Y)]
    (hcard : Nat.card (fixedPoints R Y) ≤ 2)
    (a : Subgroup.normalizer (R : Set G))
    (ha : a ∈ commutator (Subgroup.normalizer (R : Set G))) :
    ∀ y ∈ fixedPoints R Y, (a : G) • y = y := by
  apply (FixedSetNormalizerHom.mem_ker_iff G Y R a).mp
  exact TwoPointActionCommutator.apply_eq_one
    (FixedSetNormalizerHom.fixedPermHom G Y R) hcard a ha

end FiveTransitive.TwoFixedNormalizerCommutator

end CFSG
