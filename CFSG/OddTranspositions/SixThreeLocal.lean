module

public import CFSG.OddTranspositions.SixOneTwo
public import CFSG.OddTranspositions.UInDU

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem normal_le_center_of_secondKindTriangle (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hm : 3 < orderOf (u * w))
    {N : Subgroup G} (hN : N.Normal) (hNo : Odd (Nat.card N))
    (huxD : ∀ x ∈ N, x ≠ 1 → u * x * u = x⁻¹ → u * x ∈ D) :
    N ≤ Subgroup.center G := by
  have hD : IsOddTransp D := hS.oddT
  have hNset : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx =>
    CFSG.Timmesfeld.conj_mem_of_isClass hS.isClass g hx
  refine normal_le_center_of_mem_closure_commSet hS hN hNo htri.1 ?_ huxD
  exact u_mem_closure_commSet hD hNset htri h4 hno hm

end CFSG.OddTranspositions
