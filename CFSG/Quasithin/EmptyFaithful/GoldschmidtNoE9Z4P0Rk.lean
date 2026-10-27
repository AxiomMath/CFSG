module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Grp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P0Nil

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

theorem one_le_rk_fixV_of_orderOf_four (h : E9Z4Str X Tb P) {x : MulAut V}
    (hx4 : orderOf x = 4) : 1 ≤ rk (fixV (Subgroup.zpowers x)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have hmod := card_modEq_card_fixV (V := V) hP
  rw [h.card_V, card_eq_two_pow h.sq] at hmod
  by_contra h0
  have h00 : rk (fixV (Subgroup.zpowers x)) = 0 := by omega
  rw [h00] at hmod
  exact absurd hmod (by decide)

theorem two_le_rk_commV (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X) (hx1 : x ≠ 1) :
    2 ≤ rk (commV (Subgroup.zpowers x)) := by
  rcases h.orderOf_mem hx with e | e | e | e
  · exact absurd (orderOf_eq_one_iff.mp e) hx1
  · exact (h.rk_commV_involution hx e).ge
  · have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, e]
    obtain ⟨-, -, -, m, hm⟩ := commV_card_three h.sq hcard
    have hne : rk (commV (Subgroup.zpowers x)) ≠ 0 := fun h0 =>
      hx1 (eq_one_of_commV_eq_bot ((rk_eq_zero_iff h.sq).mp h0))
    omega
  · have hx4 : x ^ 4 = 1 := by rw [← e]; exact pow_orderOf_eq_one x
    have hu2 : orderOf (x ^ 2) = 2 := by rw [orderOf_pow' _ (by norm_num), e]; norm_num
    have hrk := h.rk_commV_involution (X.pow_mem hx 2) hu2
    have hle : commV (Subgroup.zpowers (x ^ 2)) ≤ commV (Subgroup.zpowers x) :=
      commV_mono216 (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2))
    have := rk_mono hle
    omega

theorem rk_fixV_of_orderOf_four (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X)
    (hx4 : orderOf x = 4) : rk (fixV (Subgroup.zpowers x)) = 1 := by
  have hx4' : x ^ 4 = 1 := by rw [← hx4]; exact pow_orderOf_eq_one x
  have hu2 : orderOf (x ^ 2) = 2 := by rw [orderOf_pow' _ (by norm_num), hx4]; norm_num
  have hrku := h.rk_commV_involution (X.pow_mem hx 2) hu2
  have hsum := rk_commV_add_rk_fixV x
  rw [h.rk_four] at hsum
  have hge := h.one_le_rk_fixV_of_orderOf_four hx4
  by_contra hne
  have hmono : commV (Subgroup.zpowers (x ^ 2)) ≤ commV (Subgroup.zpowers x) :=
    commV_mono216 (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2))
  have heq : commV (Subgroup.zpowers (x ^ 2)) = commV (Subgroup.zpowers x) :=
    eq_of_le_of_rk_le h.sq hmono (by omega)
  have h1 : commSeries (Subgroup.zpowers x) (1 + 1) = commSeries (Subgroup.zpowers x) 1 := by
    rw [commSeries_two h.sq, commSeries_one, heq]
  have h2 := commSeries_succ_succ_of_eq x h1
  have h3 := commSeries_succ_succ_of_eq x h2
  have h4 := commSeries_four_eq_bot h.sq hx4'
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, h3, h2, h1, commSeries_one] at h4
  have h5 := rk_mono hmono
  rw [h4, rk_bot] at h5
  omega

end E9Z4Str

end CFSG.Quasithin
