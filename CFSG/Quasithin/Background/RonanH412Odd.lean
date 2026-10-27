module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH412

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.RonanH49

theorem card_fixV_rho_le_eight_of_three {a b : ↥SL32} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 8 := by
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, rfl⟩ := exists_eq_conj_c3m hb hb1
    rw [card_fixV_rho_swap, card_fixV_rho_conj_left, card_fixV_rho]
    exact card_filter_c3m_one.le
  · obtain ⟨g, rfl⟩ := exists_eq_conj_c3m ha ha1
    by_cases hb1 : b = 1
    · subst hb1
      rw [card_fixV_rho_conj_left, card_fixV_rho]
      exact card_filter_c3m_one.le
    · obtain ⟨h, rfl⟩ := exists_eq_conj_c3m hb hb1
      rw [card_fixV_rho_conj, card_fixV_rho]
      exact card_filter_c3m_c3m.le

theorem card_fixV_rho_le_eight_of_seven {a b : ↥SL32} (ha : a ^ 7 = 1) (hb : b ^ 7 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 8 := by
  have h1 : ∀ r : ↥SL32, (r = slOfMat s7m det_s7m ∨ r = slOfMat s7i det_s7i) →
      Nat.card ↥(fixV (Subgroup.zpowers (rho (r, 1)))) ≤ 8 := by
    rintro r (rfl | rfl)
    · rw [card_fixV_rho]
      exact card_filter_s7m_one.le.trans (by norm_num)
    · rw [card_fixV_rho]
      exact card_filter_s7i_one.le.trans (by norm_num)
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hg, card_fixV_rho_swap,
      card_fixV_rho_conj_left]
    · exact h1 _ (Or.inl rfl)
    · exact h1 _ (Or.inr rfl)
  · obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m ha ha1
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inl rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7m_s7m
        · exact card_filter_s7m_s7i
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inr rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7i_s7m
        · exact card_filter_s7i_s7i

theorem card_fixV_le_eight_of_odd {y : MulAut WMod} (hy : y ∈ norm) (hy1 : y ≠ 1)
    (ho : Odd (orderOf y)) : Nat.card ↥(fixV (Subgroup.zpowers y)) ≤ 8 := by
  have hfin : Finite (MulAut WMod) := MulEquiv.finite_left
  obtain ⟨g, rfl⟩ := mem_img_of_odd hy ho
  set n := orderOf (rho g) with hn
  have hng : n = orderOf g := orderOf_injective rho rho_injective g
  have hn0 : n ≠ 0 := (orderOf_pos (rho g)).ne'
  have hn1 : n ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have hdvd : n ∣ 168 ^ 2 := by
    rw [hng]
    have h := orderOf_dvd_natCard g
    rwa [Nat.card_prod, card_SL32, ← sq] at h
  have h37 : 3 ∣ n ∨ 7 ∣ n := by
    by_contra hno
    push Not at hno
    have hc2 : Nat.Coprime n 2 := ho.coprime_two_right
    have hc3 : Nat.Coprime n 3 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr hno.1))
    have hc7 : Nat.Coprime n 7 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).mpr hno.2))
    have hc : Nat.Coprime n (168 ^ 2) := by
      have e : (168 : ℕ) ^ 2 = 2 ^ 6 * 3 ^ 2 * 7 ^ 2 := by norm_num
      rw [e]
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc2.pow_right 6) (hc3.pow_right 2))
        (hc7.pow_right 2)
    exact hn1 (Nat.Coprime.eq_one_of_dvd hc hdvd)
  have key : ∀ p : ℕ, p ∣ n → (p = 3 ∨ p = 7) →
      Nat.card ↥(fixV (Subgroup.zpowers (rho g))) ≤ 8 := by
    intro p hp hp37
    have hpo : orderOf (rho g ^ (n / p)) = p := orderOf_pow_orderOf_div hn0 hp
    obtain ⟨g', hg'⟩ : ∃ g', g' = g ^ (n / p) := ⟨_, rfl⟩
    have hrho : rho g ^ (n / p) = rho g' := by rw [hg', map_pow]
    have hg'p : g' ^ p = 1 := by
      have h1 := pow_orderOf_eq_one (rho g ^ (n / p))
      rw [hpo, hrho] at h1
      apply rho_injective
      rw [map_pow, h1, map_one]
    have hg'1 : g' ≠ 1 := fun h => by
      rw [hrho, h, map_one, orderOf_one] at hpo
      rcases hp37 with rfl | rfl <;> omega
    have hle : fixV (Subgroup.zpowers (rho g)) ≤ fixV (Subgroup.zpowers (rho g')) := by
      refine CFSG.Quasithin.B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ?_)
      rw [← hrho]
      exact (Subgroup.zpowers (rho g)).pow_mem (Subgroup.mem_zpowers (rho g)) _
    refine (Subgroup.card_le_of_le hle).trans ?_
    have hab : (g'.1, g'.2) ≠ 1 := hg'1
    rcases hp37 with rfl | rfl
    · exact card_fixV_rho_le_eight_of_three (by rw [← Prod.pow_fst, hg'p]; rfl)
        (by rw [← Prod.pow_snd, hg'p]; rfl) hab
    · exact card_fixV_rho_le_eight_of_seven (by rw [← Prod.pow_fst, hg'p]; rfl)
        (by rw [← Prod.pow_snd, hg'p]; rfl) hab
  rcases h37 with h | h
  · exact key 3 h (Or.inl rfl)
  · exact key 7 h (Or.inr rfl)

theorem isPGroup_cent_of_rkIdx_lt (U : Subgroup WMod) (hU : rkIdx U < 6) :
    IsPGroup 2 ↥(GW ⊓ centSub U) := by
  have hfin : Finite (MulAut WMod) := MulEquiv.finite_left
  have hWcard : Nat.card WMod = 2 ^ 9 := by
    show Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 2 ^ 9
    rw [Matrix.card_matrix, Nat.card_zmod, Nat.card_fin] <;> norm_num
  have hrkW : rk WMod = 9 := by
    show padicValNat 2 (Nat.card WMod) = 9
    rw [hWcard, padicValNat.prime_pow]
  have hrk : rk ↥U + rkIdx U = rk WMod := rk_add_rkIdx U
  have hU16 : 16 ≤ Nat.card ↥U := by
    have h1 : 4 ≤ rk ↥U := by omega
    have h2 : 2 ^ rk ↥U ≤ Nat.card ↥U := Nat.le_of_dvd Nat.card_pos pow_padicValNat_dvd
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ rk ↥U := Nat.pow_le_pow_right (by norm_num) h1
      _ ≤ Nat.card ↥U := h2
  have hC : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card ↥(GW ⊓ centSub U) → d = 2 := by
    intro d hd hdC
    by_contra hne
    have hodd : Odd d := hd.odd_of_ne_two hne
    haveI hfact : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdC
    have hxC : (x : MulAut WMod) ∈ GW ⊓ centSub U := x.2
    have hord : orderOf (x : MulAut WMod) = d := by
      rw [Subgroup.orderOf_coe, hx]
    have hx1 : (x : MulAut WMod) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      exact hd.one_lt.ne hord
    have hnorm : (x : MulAut WMod) ∈ norm := by
      rw [← GW_eq_norm]
      exact (Subgroup.mem_inf.1 hxC).1
    have hcentU : (x : MulAut WMod) ∈ centSub U := (Subgroup.mem_inf.1 hxC).2
    have hodd' : Odd (orderOf (x : MulAut WMod)) := by
      rw [hord]
      exact hodd
    have hfix := card_fixV_le_eight_of_odd hnorm hx1 hodd'
    have hle : U ≤ fixV (Subgroup.zpowers (x : MulAut WMod)) := by
      intro u hu
      refine CFSG.Quasithin.mem_fixV.2 ?_
      intro z hz
      have hzC : z ∈ centSub U := Subgroup.zpowers_le.mpr hcentU hz
      exact CFSG.Quasithin.mem_centSub.1 hzC u hu
    have hle' := Subgroup.card_le_of_le hle
    omega
  exact IsPGroup.iff_card.mpr
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥(GW ⊓ centSub U))).ne' hC⟩

end CFSG.Quasithin.RonanH412
