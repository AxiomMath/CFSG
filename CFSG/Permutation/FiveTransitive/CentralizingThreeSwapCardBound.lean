module

public import CFSG.Permutation.FiveTransitive.LargeCentralizerFree
public import CFSG.Permutation.FiveTransitive.FreeThreeSwapObstruction

public section

namespace CFSG

namespace FiveTransitive.CentralizingThreeSwapCardBound

open MulAction FixedNormalizerAction

theorem card_le_seven
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (B : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (himage : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) =
      ThreeSwapTwoGroup.subgroup e)
    (heven : ∀ b : B, Equiv.Perm.sign (toPerm b.val.val : Equiv.Perm X) = 1)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (hcentral : ∀ b : B, ∀ q : Q, Commute b.val.val q.val)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1) :
    Nat.card Q ≤ 7 := by
  by_contra hQ
  exact FreeThreeSwapObstruction.not_free Q B hB e himage heven
    (LargeCentralizerFree.free Q B hB 7 (by omega) hmax hcentral hfree)

end FiveTransitive.CentralizingThreeSwapCardBound

end CFSG
