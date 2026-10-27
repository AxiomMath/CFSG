module

public import CFSG.Permutation.FiveTransitive.CyclicNormalizerAlternating
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.CyclicFixedNormalizerAlternating

open MulAction FixedNormalizerAction

variable {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G)

theorem seven_alternating_le_centralizer_image [Fintype (Fixed (X := X) Q)]
    [DecidableEq (Fixed (X := X) Q)]
    (hcyclic : IsCyclic Q) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤) :
    alternatingGroup (Fixed (X := X) Q) ≤
      ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) := by
  let := hcyclic
  exact CyclicNormalizerAlternating.alternating_le_centralizer_image Q (by omega)
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (MonoidHom.range_eq_top.mp himage)

end FiveTransitive.CyclicFixedNormalizerAlternating

end CFSG
