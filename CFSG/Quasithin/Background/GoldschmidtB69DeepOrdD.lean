module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepOrdC
public import CFSG.Quasithin.Background.GoldschmidtB69DeepFam

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

namespace B69

namespace E22FamC

section Cases

variable {F : Type} [Group F] {x k : ℕ} (hx4 : 4 ≤ x) (hx6 : x ^ 6 = 2 ^ k)
  (hd : 2 ^ k ∣ Nat.card F) (hle : Nat.card F ≤ x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)))
include hx4 hx6 hd hle

theorem g2_psl3_two {m : ℕ} (hm1 : 1 ≤ m) (hm : IsPSL 3 2 m F) : False := by
  have h1 := card_psl_three_mul hm
  have hg : Nat.gcd 3 (2 ^ m - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hev : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hQ2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  set Q := 2 ^ m with hQdef
  have hod : Odd ((Q ^ 2 - 1) * (Q ^ 3 - 1)) :=
    Odd.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hev.pow_of_ne_zero (by norm_num))
      odd_one) (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega))
        (hev.pow_of_ne_zero (by norm_num)) odd_one)
  have hd2 : 2 ^ k ∣ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) := by
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  have h5 : x ^ 6 ≤ Q ^ 3 := by
    rw [hx6]
    exact Nat.le_of_dvd (by positivity) (two_pow_dvd_of_odd_mul hod hd2)
  have hQx : x ^ 2 ≤ Q := by
    have : (x ^ 2) ^ 3 ≤ Q ^ 3 := by
      calc (x ^ 2) ^ 3 = x ^ 6 := by ring
        _ ≤ Q ^ 3 := h5
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  have := unit_ineq hx4 hQx hg (Or.inr h1)
  omega

theorem g2_psp4 {m : ℕ} (hm1 : 1 ≤ m) (hm : E2.IsSp4Prime m F) : False := by
  unfold E2.IsSp4Prime at hm
  split_ifs at hm with h1
  · obtain ⟨e⟩ := hm
    have hc' : Nat.card F = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hc'] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    rw [← hx6] at this
    have h6 : 4 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx4 6
    norm_num at h6
    omega
  · have hc' := card_psp_four hm
    have hev : Even (2 ^ m) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have hQ4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    set Q := 2 ^ m with hQdef
    have hod : Odd ((Q ^ 2 - 1) * (Q ^ 4 - 1)) :=
      Odd.mul (Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega))
        (hev.pow_of_ne_zero (by norm_num)) odd_one) (Nat.Even.sub_odd
          (Nat.one_le_pow _ _ (by omega)) (hev.pow_of_ne_zero (by norm_num)) odd_one)
    rw [hc'] at hd
    have h5 : x ^ 6 ≤ Q ^ 4 := by
      rw [hx6]
      exact Nat.le_of_dvd (by positivity) (two_pow_dvd_of_odd_mul hod hd)
    have hQx : x ^ 3 ≤ Q ^ 2 := by
      have : (x ^ 3) ^ 2 ≤ (Q ^ 2) ^ 2 := by
        calc (x ^ 3) ^ 2 = x ^ 6 := by ring
          _ ≤ Q ^ 4 := h5
          _ = (Q ^ 2) ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    have := sp4_ineq hx4 hQx
    rw [hc'] at hle
    omega

theorem g2_psu_odd {p : ℕ} (hp2 : p ≠ 2) (hp4 : p % 4 = 1)
    (hp : IsPSU 3 p 1 F) : False := by
  have hpp : p.Prime := hp.1.1
  have hodd : Odd p := hpp.eq_two_or_odd'.resolve_left hp2
  have h1 := card_psu_three_mul hp
  rw [pow_one] at h1
  have hg : Nat.gcd 3 (p + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  obtain ⟨u, rfl⟩ : ∃ u, p = u + 1 := ⟨p - 1, by have := hpp.two_le; omega⟩
  have hu2 : 2 ≤ u := by
    have := hpp.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  have e1 : (u + 1) ^ 2 - 1 = u * (u + 2) := by
    have : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    omega
  have e2 : (u + 1) ^ 3 + 1 = (u + 2) * (u ^ 2 + u + 1) := by ring
  have hod : Odd (u ^ 2 + u + 1) := by
    have : Even (u ^ 2 + u) := by
      have h' : u ^ 2 + u = u * (u + 1) := by ring
      rw [h']
      exact Nat.even_mul_succ_self u
    exact this.add_one
  have hd2 : 2 ^ k ∣ (u + 1) ^ 3 * (u * (u + 2) * ((u + 2) * (u ^ 2 + u + 1))) := by
    rw [e1, e2] at h1
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  have hd3 : 2 ^ k ∣ u * (u + 2) * ((u + 2) * (u ^ 2 + u + 1)) :=
    two_pow_dvd_of_odd_mul' (hodd.pow) hd2
  have hd4 : 2 ^ k ∣ u * (u + 2) * (u + 2) := by
    have : u * (u + 2) * ((u + 2) * (u ^ 2 + u + 1)) =
        (u * (u + 2) * (u + 2)) * (u ^ 2 + u + 1) := by ring
    rw [this] at hd3
    exact two_pow_dvd_of_odd_mul hod hd3
  have h5 : x ^ 6 ≤ u * (u + 2) * (u + 2) := by
    rw [hx6]
    exact Nat.le_of_dvd (by positivity) hd4
  have h6' : x ^ 6 < (u + 2) ^ 3 := by
    have : u * (u + 2) * (u + 2) < (u + 2) ^ 3 := by nlinarith
    omega
  have hQx : x ^ 2 ≤ u + 1 := by
    have : (x ^ 2) ^ 3 < (u + 2) ^ 3 := by
      calc (x ^ 2) ^ 3 = x ^ 6 := by ring
        _ < (u + 2) ^ 3 := h6'
    have := (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
    omega
  rw [e1, e2] at h1
  have := unit_ineq hx4 hQx hg (Or.inl (by rw [e1, e2]; exact h1))
  omega

theorem g2_psl3_odd {p : ℕ} (hp2 : p ≠ 2) (hp4 : p % 4 = 3) (hp : IsPSL 3 p 1 F) : False := by
  have hpp : p.Prime := hp.1.1
  have hodd : Odd p := hpp.eq_two_or_odd'.resolve_left hp2
  have h1 := card_psl_three_mul hp
  rw [pow_one] at h1
  have hg : Nat.gcd 3 (p - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  obtain ⟨u, rfl⟩ : ∃ u, p = u + 1 := ⟨p - 1, by have := hpp.two_le; omega⟩
  have hu2 : 2 ≤ u := by
    have := hpp.two_le
    obtain ⟨k, hk⟩ := hodd
    omega
  have e1 : (u + 1) ^ 2 - 1 = u * (u + 2) := by
    have : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    omega
  have e2 : (u + 1) ^ 3 - 1 = u * (u ^ 2 + 3 * u + 3) := by
    have : (u + 1) ^ 3 = u * (u ^ 2 + 3 * u + 3) + 1 := by ring
    omega
  have hod : Odd (u ^ 2 + 3 * u + 3) := by
    have h' : u ^ 2 + 3 * u = u * (u + 1) + 2 * u := by ring
    have : Even (u ^ 2 + 3 * u) := by
      rw [h']
      exact (Nat.even_mul_succ_self u).add (even_two_mul u)
    exact this.add_odd ⟨1, by norm_num⟩
  have hd2 : 2 ^ k ∣ (u + 1) ^ 3 * (u * (u + 2) * (u * (u ^ 2 + 3 * u + 3))) := by
    rw [e1, e2] at h1
    rw [← h1]
    exact Dvd.dvd.mul_right hd _
  have hd3 : 2 ^ k ∣ u * (u + 2) * (u * (u ^ 2 + 3 * u + 3)) :=
    two_pow_dvd_of_odd_mul' (hodd.pow) hd2
  have hd4 : 2 ^ k ∣ u * (u + 2) * u := by
    have : u * (u + 2) * (u * (u ^ 2 + 3 * u + 3)) =
        (u * (u + 2) * u) * (u ^ 2 + 3 * u + 3) := by ring
    rw [this] at hd3
    exact two_pow_dvd_of_odd_mul hod hd3
  have h5 : x ^ 6 ≤ u * (u + 2) * u := by
    rw [hx6]
    exact Nat.le_of_dvd (by positivity) hd4
  have h6' : x ^ 6 < (u + 2) ^ 3 := by
    have : u * (u + 2) * u < (u + 2) ^ 3 := by nlinarith
    omega
  have hQx : x ^ 2 ≤ u + 1 := by
    have : (x ^ 2) ^ 3 < (u + 2) ^ 3 := by
      calc (x ^ 2) ^ 3 = x ^ 6 := by ring
        _ < (u + 2) ^ 3 := h6'
    have := (Nat.pow_lt_pow_iff_left (by norm_num)).1 this
    omega
  rw [e1, e2] at h1
  have := unit_ineq hx4 hQx hg (Or.inr (by rw [e1, e2]; exact h1))
  omega

end Cases

theorem not_card_g2 {F : Type} [Group F] (hF : E22FamC F) {n : ℕ}
    (hn : 2 ≤ n) {c : ℕ} (hc : Odd c)
    (h : Nat.card F * c = (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))) : False := by
  have hx6 : (2 ^ n) ^ 6 = 2 ^ (6 * n) := by rw [← pow_mul, mul_comm]
  have hx4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set x := 2 ^ n with hxdef
  have h6 : 4 ^ 6 ≤ x ^ 6 := Nat.pow_le_pow_left hx4 6
  have hpos : 0 < x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) := by
    have h2 : 0 < x ^ 6 - 1 := by norm_num at h6; omega
    have h16 : 16 ≤ x ^ 2 := by nlinarith
    have h3 : 0 < x ^ 2 - 1 := by omega
    exact Nat.mul_pos (by positivity) (Nat.mul_pos h2 h3)
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by intro h0; rw [h0] at h; omega)
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h0
    · omega
    · exact h0
  have hle : Nat.card F ≤ x ^ 6 * ((x ^ 6 - 1) * (x ^ 2 - 1)) := by nlinarith
  have hd : 2 ^ (6 * n) ∣ Nat.card F := by
    apply two_pow_dvd_of_odd_mul hc
    rw [h, ← hx6]
    exact Dvd.intro _ rfl
  rcases hF with ⟨p, e, hp⟩ | ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨m, hm1, hm⟩ | ⟨m, hm1, hm⟩ | ⟨p, hp2, hp4, hp⟩ |
    ⟨p, hp2, hp4, hp⟩
  · exact g2_psl2 hx4 hx6 hd hle hp
  · exact g2_sz hx4 hx6 hd hle hm
  · exact g2_psu_two hx4 hx6 hd hle hm
  · exact g2_psl3_two hx4 hx6 hd hle hm1 hm
  · exact g2_psp4 hx4 hx6 hd hle hm1 hm
  · exact g2_psu_odd hx4 hx6 hd hle hp2 hp4 hp
  · exact g2_psl3_odd hx4 hx6 hd hle hp2 hp4 hp

end E22FamC

end B69

end CFSG.Quasithin
