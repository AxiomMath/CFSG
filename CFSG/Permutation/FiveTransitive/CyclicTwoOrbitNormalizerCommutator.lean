module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerAlternating
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG

namespace FiveTransitive.CyclicTwoOrbitNormalizerCommutator

open MulAction NormalizerFixedComplement

theorem centralizes
    {G : Type*} [Group G] (Q : Subgroup G) [IsCyclic Q]
    (R : Subgroup (Normalizer Q))
    (a : Subgroup.normalizer (R : Set (Normalizer Q)))
    (ha : a ∈ commutator (Subgroup.normalizer (R : Set (Normalizer Q)))) :
    a.val.val ∈ Subgroup.centralizer (Q : Set G) := by
  have hm : (commutator (Subgroup.normalizer (R : Set (Normalizer Q)))).map
      (Subgroup.normalizer (R : Set (Normalizer Q))).subtype ≤
      commutator (Normalizer Q) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact CyclicNormalizerAlternating.commutator_le_centralizer Q (hm ⟨a, ha, rfl⟩)

end FiveTransitive.CyclicTwoOrbitNormalizerCommutator

end CFSG
