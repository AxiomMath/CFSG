module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardH
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallIndexCases

namespace CFSG
end CFSG
open CFSG

/-!
# The two group-order cases in the Brauer--Suzuki--Wall argument
-/

namespace CFSG.GorensteinWalter

universe u

/-- The character-theoretic index alternatives give Bender's two group-order
alternatives after multiplying by `|H| = 2|K|`. -/
public theorem BrauerSuzukiWallHypotheses.order_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) :
    let k := Nat.card h.K
    Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
      Nat.card G = (2 * k - 1) * (k - 1) * (2 * k) := by
  dsimp only
  rcases h.index_cases hk with hplus | hminus
  · left
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * Nat.card h.K) *
          ((2 * Nat.card h.K + 1) * (Nat.card h.K + 1)) := by
        rw [h.card_H, hplus]
      _ = (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) *
          (2 * Nat.card h.K) := by ac_rfl
  · right
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * Nat.card h.K) *
          ((2 * Nat.card h.K - 1) * (Nat.card h.K - 1)) := by
        rw [h.card_H, hminus]
      _ = (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) *
          (2 * Nat.card h.K) := by ac_rfl

end CFSG.GorensteinWalter
