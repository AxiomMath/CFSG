module

public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.F8G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

namespace HypF91

variable {T V L V₁ Vp H : Subgroup G}

theorem almostSpecialHyp (h : HypF91 T V L V₁ Vp H) : AlmostSpecialHyp Vp V₁ L T H where
  elemAbelian := h.elemAbelian_Vp
  ne_bot := h.V₁_ne_bot
  le_V := h.V₁_le_Vp
  oTwo_eq := by rw [← oTwoRes_eq_oTwoUpper]; exact h.oTwoRes_eq.symm
  V_le_T := h.Vp_le_T
  T_le_normV₁ := h.T_normalizes_V₁
  T_le_normV := h.T_normalizes_Vp
  T_le_normL := h.normalizes_L
  sylow_LT := h.sylow_LT
  H_le := h.H_normalizes_V₁
  lOne_sup_le := by rw [lOne_eq_L₁Of]; exact h.L₁T_le_H
  sylow_H := h.sylow_H
  charTwo := h.charTwo_H
  irred := by
    rw [lOne_eq_L₁Of]
    exact ⟨h.V₁_lt_Vp, h.L₁T_normalizes_Vp, h.L₁T_le_H.trans h.H_normalizes_V₁, h.irred⟩

end HypF91

end CFSG.Quasithin
