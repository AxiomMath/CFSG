module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint

theorem ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (hS : Nonempty (S ≃* NativeSporadic.M11) ∨ Nonempty (S ≃* NativeSporadic.M12) ∨
      Nonempty (S ≃* NativeSporadic.M22) ∨ Nonempty (S ≃* NativeSporadic.M23) ∨
      Nonempty (S ≃* NativeSporadic.M24))
    (hC : Subgroup.centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  rcases hS with h | h | h | h | h
  · obtain ⟨ψ⟩ := h
    exact oddCore_centralizer_eq_bot_of_normal m11_inner_oddCore
      (m11_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))) m11_outer_oddCore S ψ hC
      t ht
  · obtain ⟨ψ⟩ := h
    exact oddCore_centralizer_eq_bot_of_normal m12_inner_oddCore m12_mulAut_card
      m12_outer_oddCore S ψ hC t ht
  · obtain ⟨ψ⟩ := h
    exact oddCore_centralizer_eq_bot_of_normal m22_inner_oddCore m22_mulAut_card
      m22_outer_oddCore S ψ hC t ht
  · obtain ⟨ψ⟩ := h
    exact oddCore_centralizer_eq_bot_of_normal m23_inner_oddCore
      (m23_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))) m23_outer_oddCore S ψ hC
      t ht
  · obtain ⟨ψ⟩ := h
    exact oddCore_centralizer_eq_bot_of_normal m24_inner_oddCore
      (m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))) m24_outer_oddCore S ψ hC
      t ht

end CFSG.Sporadic.Schreier
