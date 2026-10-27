module

public import CFSG.Walter.ReeOrder.Ward.Construct
public import CFSG.Walter.ReeOrder.Ward.PSLThree
public import CFSG.Walter.ReeOrder.Ward.PSLFive
public import CFSG.Walter.ReeOrder.Ward.PSLToWard

public section

open scoped MatrixGroups

namespace CFSG.Walter.Ward

theorem wardLTable : WardLTable := by
  intro F _ _ _ q hq hF hq7 h8
  subst hq
  rcases h8 with h8 | h8
  · have he : wardSign (Fintype.card F) = -1 := by
      unfold wardSign
      rw [ite_eq_left h8]
    rw [he]
    obtain ⟨D⟩ := PSLTable.exists_pslData_three hF hq7 h8
    exact ⟨D.toWardL⟩
  · have he : wardSign (Fintype.card F) = 1 := by
      unfold wardSign
      rw [ite_eq_right (by omega)]
    rw [he]
    obtain ⟨D⟩ := PSLTable.exists_pslData_five hF hq7 h8
    exact ⟨D.toWardL⟩

theorem ward_order
    {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G) :
    (∃ k ≥ 1, h.q = 3 ^ (2 * k + 1)) ∧ Nat.card G = h.q ^ 3 * (h.q ^ 3 + 1) * (h.q - 1) :=
  (ward_order_of_table wardLTable h).2

theorem ward_sign
    {G : Type} [Group G] [Finite G] (h : ReeTypeHyp G) : h.e = -1 :=
  (ward_order_of_table wardLTable h).1

end CFSG.Walter.Ward
