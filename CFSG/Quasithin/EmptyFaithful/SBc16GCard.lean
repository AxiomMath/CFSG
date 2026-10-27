module

public import CFSG.Quasithin.EmptyFaithful.S14612DA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace SBc16

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem card_H₀_eq (hp0 : p ≠ 0) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card H₀ = 4 * p ^ 2 * Nat.card (pCoreOf 2 H) := by
  have hmul := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h.H₁_le_normalizer_H₂
  rw [← h.sup, h.inf, h.card_H₁_gen hp0, h.swap.card_H₁_gen hp0] at hmul
  have hQ : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hQ ?_
  rw [hmul]
  ring

theorem card_H_eq (hp0 : p ≠ 0) (h : IsDecP T M H p H₀ H₁ H₂ t) (hidx : H₀.relIndex H = 2) :
    Nat.card H = 8 * p ^ 2 * Nat.card (pCoreOf 2 H) := by
  have h1 := Subgroup.relIndex_mul_card H₀ H
  rw [inf_eq_left.mpr h.le, hidx, card_H₀_eq hp0 h] at h1
  rw [← h1]
  ring

theorem card_T_eq (S : Setting146 G T M) {PQ : Subgroup G} (hp5 : p = 5) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (hidx : H₀.relIndex H = 2) :
    Nat.card T = 8 * Nat.card (pCoreOf 2 H) := by
  subst hp5
  have hTH : T ≤ H := hred.isHTM.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := hTsyl.isPGroup.to_le (S.pCoreOf_le_T hred.isHTM)
  have hcard := card_H_eq (by norm_num) h hidx
  rw [hTsyl.card_eq]
  exact twoPart_eq_of_card_eq_odd_mul (a := 3) (m := 25) hQ2 (by decide) (by rw [hcard]; ring)

end SBc16

end CFSG.Quasithin
