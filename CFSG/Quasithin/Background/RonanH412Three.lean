module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH412

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.RonanH49

theorem card_fixV_rho_eq_eight_of_three {a b : ↥SL32} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) = 8 := by
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, rfl⟩ := exists_eq_conj_c3m hb hb1
    rw [card_fixV_rho_swap, card_fixV_rho_conj_left, card_fixV_rho]
    exact card_filter_c3m_one
  · obtain ⟨g, rfl⟩ := exists_eq_conj_c3m ha ha1
    by_cases hb1 : b = 1
    · subst hb1
      rw [card_fixV_rho_conj_left, card_fixV_rho]
      exact card_filter_c3m_one
    · obtain ⟨h, rfl⟩ := exists_eq_conj_c3m hb hb1
      rw [card_fixV_rho_conj, card_fixV_rho]
      exact card_filter_c3m_c3m

theorem card_fixV_eq_eight_of_three {y : MulAut WMod} (hy : y ∈ norm) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers y)) = 8 := by
  have hfin : Finite (MulAut WMod) := MulEquiv.finite_left
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hodd : Odd (orderOf y) := by rw [hord]; exact ⟨1, by norm_num⟩
  obtain ⟨g, rfl⟩ := mem_img_of_odd hy hodd
  have hg3 : g ^ 3 = 1 :=
    rho_injective (((map_pow rho g 3).trans hy3).trans (map_one rho).symm)
  refine card_fixV_rho_eq_eight_of_three ?_ ?_ ?_
  · rw [← Prod.pow_fst, hg3]
    rfl
  · rw [← Prod.pow_snd, hg3]
    rfl
  · intro h
    apply hy1
    have : g = 1 := h
    rw [this, map_one]

end CFSG.Quasithin.RonanH412
