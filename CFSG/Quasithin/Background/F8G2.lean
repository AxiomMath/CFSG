module

public import CFSG.Quasithin.Background.F8Basic
public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

theorem oTwoRes_eq_oTwoUpper (X : Subgroup G) : oTwoRes X = oTwoUpper X := by
  unfold oTwoRes oTwoUpper
  congr 1
  ext x
  constructor
  · rintro ⟨hx, m, hm, hxm⟩
    exact ⟨hx, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hxm)⟩
  · rintro ⟨hx, ho⟩
    exact ⟨hx, orderOf x, ho, pow_orderOf_eq_one x⟩

theorem lOne_eq_L₁Of (L V₁ : Subgroup G) : lOne L V₁ = L₁Of L V₁ :=
  (oTwoRes_eq_oTwoUpper _).symm

namespace HypF81

variable {T V L V₁ H : Subgroup G}

theorem almostSpecialHyp (h : HypF81 T V L V₁ H) : AlmostSpecialHyp V V₁ L T H where
  elemAbelian := h.elemAbelian
  ne_bot := h.V₁_ne_bot
  le_V := h.V₁_le_V
  oTwo_eq := by rw [← oTwoRes_eq_oTwoUpper]; exact h.oTwoRes_eq.symm
  V_le_T := h.V_le_T
  T_le_normV₁ := h.T_normalizes_V₁
  T_le_normV := h.T_normalizes_V
  T_le_normL := h.normalizes_L
  sylow_LT := h.sylow_LT
  H_le := h.H_normalizes_V₁
  lOne_sup_le := by rw [lOne_eq_L₁Of]; exact h.L₁T_le_H
  sylow_H := h.sylow_H
  charTwo := h.charTwo_H
  irred := by
    rw [lOne_eq_L₁Of]
    exact ⟨h.V₁_lt_V, h.L₁T_normalizes_V, h.L₁T_le_H.trans h.H_normalizes_V₁, h.irred⟩

end HypF81

end CFSG.Quasithin
