module

public import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim

import CFSG.Quasithin.Background.Harris.L2.Numerics
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_three_mul_of_mul_two_pow_eq {m d r : ℕ} {J : Finset ℕ} (hr : 0 < r) (hrm : r < m)
    (hJ : J.Nonempty) (hJm : ∀ i ∈ J, i < m) (hd : J.image (fun i => (i + d) % m) = J)
    (h : d * 2 ^ J.card = 2 * m + 2 * r) : m = 3 * r ∧ d = r ∧ J.card = 3 := by
  have hm : 0 < m := by omega
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0] at h
      simp at h
      omega
    · exact hpos
  set g := Nat.gcd m d with hg
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left d hm
  set t := m / g with ht
  have hgt : g * t = m := by
    rw [ht, hg]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m d)
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · rw [h0] at hgt
      simp at hgt
      omega
    · exact hpos
  set s := d / g with hs
  have hds : d = g * s := by
    rw [hs, hg]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right m d)).symm
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · rw [h0] at hds
      simp at hds
      omega
    · exact hpos
  set k := J.card with hk
  have hk1 : 1 ≤ k := by
    rw [hk]
    have hpos := Finset.card_pos.mpr hJ
    omega
  have htle : t ≤ k := by
    rw [hk, ht, hg]
    exact div_gcd_le_card_of_image_add_mod (by omega) hJ hJm hd
  have hstep : d * 2 ^ (k - 1) = m + r := by
    have h2 : d * 2 ^ k = 2 * (m + r) := by omega
    have hpow : d * 2 ^ k = 2 * (d * 2 ^ (k - 1)) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
      ring
    omega
  have hmul : g * (s * 2 ^ (k - 1)) = m + r := by
    calc g * (s * 2 ^ (k - 1)) = (g * s) * 2 ^ (k - 1) := by ring
      _ = d * 2 ^ (k - 1) := by rw [← hds]
      _ = m + r := hstep
  have hlt1 : t < s * 2 ^ (k - 1) := by
    apply (Nat.mul_lt_mul_left hgpos).mp
    rw [hgt, hmul]
    omega
  have hlt2 : s * 2 ^ (k - 1) < 2 * t := by
    apply (Nat.mul_lt_mul_left hgpos).mp
    have h2m : g * (2 * t) = 2 * m := by
      rw [← hgt]
      ring
    rw [hmul, h2m]
    omega
  have hkineq : 2 ^ (k - 1) < 2 * k := by
    have hle : 2 ^ (k - 1) ≤ s * 2 ^ (k - 1) := Nat.le_mul_of_pos_left _ hs1
    calc 2 ^ (k - 1) ≤ s * 2 ^ (k - 1) := hle
      _ < 2 * t := hlt2
      _ ≤ 2 * k := Nat.mul_le_mul_left 2 htle
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have hk4 : 4 ≤ k := by omega
    have hb := CFSG.Quasithin.G11.Harris.L2.four_mul_le_two_pow (w := k) hk4
    have hpow : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1, pow_succ]
      ring
    omega
  interval_cases k
  · norm_num at h hstep hlt1 hlt2 htle
    omega
  · norm_num at h hstep hlt1 hlt2 htle
    omega
  · norm_num at h hstep hlt1 hlt2 htle
    have ht3 : t = 3 := by omega
    have hs1' : s = 1 := by omega
    rw [ht3] at hgt
    rw [hs1'] at hds
    norm_num at hgt hds hstep h
    refine ⟨?_, ?_, rfl⟩ <;> omega

theorem eq_three_mul_of_irreducible_of_relIndex {V Z L : Subgroup G} {m r : ℕ} (hr : 0 < r)
    (hrm : r < m) (hquot : IsL2Quot m (oTwoQuot ↥L)) (hVZ : Z ≤ V) (hsec : IsElemSec Z V)
    (hL : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))
    (hirr : ∀ W : Subgroup G, Z ≤ W → W ≤ V → L ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = V)
    (hnt : ∃ l ∈ L, ∃ v ∈ V, ⁅l, v⁆ ∉ Z)
    (hcard : Z.relIndex V = 2 ^ (2 * m + 2 * r)) : m = 3 * r := by
  obtain ⟨d, J, hd1, hJne, hJm, hshift, hrel⟩ :=
    exists_relIndex_eq_of_irreducible (by omega) hquot hVZ hsec hL hirr hnt
  have hpow : 2 ^ (d * 2 ^ J.card) = 2 ^ (2 * m + 2 * r) := by
    rw [← hrel, hcard]
  have h : d * 2 ^ J.card = 2 * m + 2 * r := Nat.pow_right_injective le_rfl hpow
  exact (eq_three_mul_of_mul_two_pow_eq hr hrm hJne hJm hshift h).1

end CFSG.Quasithin.St84
