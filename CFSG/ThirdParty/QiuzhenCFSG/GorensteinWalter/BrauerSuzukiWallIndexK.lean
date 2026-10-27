module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardH

namespace CFSG
end CFSG
open CFSG

/-!
# The index of `K` in the Brauer--Suzuki--Wall centralizer
-/

namespace CFSG.GorensteinWalter

universe u

/-- The abelian subgroup `K` has index two in `H = C_G(t)`. -/
public theorem BrauerSuzukiWallHypotheses.index_K_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    (h.K.subgroupOf h.H).index = 2 := by
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hKcard : Nat.card (h.K.subgroupOf h.H) = Nat.card h.K :=
    natCard_subgroupOf_eq h.K h.H hKleH
  have hmul := Subgroup.card_mul_index (h.K.subgroupOf h.H)
  rw [hKcard, h.card_H] at hmul
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := h.K))
  simpa [mul_comm] using hmul

end CFSG.GorensteinWalter
