module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoOrder
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order dichotomy in the order-two branch

When `|K| = 2`, the normalizer of the involution centralizer is `A₄`.  If
that normalizer is the whole group, the group has order twelve; otherwise the
involution count gives order sixty.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch, the ambient group has order twelve or sixty. -/
public theorem
    BrauerSuzukiWallHypotheses.card_eq_twelve_or_sixty_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) :
    Nat.card G = 12 ∨ Nat.card G = 60 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  by_cases hN : N = ⊤
  · left
    let e : N ≃* alternatingGroup (Fin 4) :=
      (h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk).some
    have hNcard : Nat.card N = 12 := by
      calc
        Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
          Nat.card_congr e.toEquiv
        _ = 12 := by
          rw [nat_card_alternatingGroup]
          norm_num [Nat.factorial]
    simpa [hN] using hNcard
  · right
    exact h.card_eq_sixty_of_card_K_eq_two_of_normalizer_ne_top hk hN

end CFSG.GorensteinWalter
