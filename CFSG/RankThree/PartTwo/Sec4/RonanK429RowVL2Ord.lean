module

public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace RowV

theorem coprime_three_quad (t : ℕ) : Nat.Coprime 3 (3 * t ^ 2 + 3 * t + 1) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h1 : 3 ∣ 3 * (t ^ 2 + t) + 1 := by
    rw [show 3 * (t ^ 2 + t) + 1 = 3 * t ^ 2 + 3 * t + 1 by ring]
    exact h
  have h2 : 3 ∣ 1 := (Nat.dvd_add_right (dvd_mul_right 3 _)).mp h1
  norm_num at h2

theorem coprime_three_lin {t r : ℕ} (hr1 : 1 ≤ r) (hr2 : r ≤ 2) : Nat.Coprime 3 (3 * t + r) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  omega

theorem pow_le_of_dvd {f u R : ℕ} (hf : 2 ≤ f) (hu : 0 < u) (hR : Nat.Coprime 3 R)
    (h : 3 ^ (f + 1) ∣ 27 * u ^ 2 * R) : 3 ^ f ≤ 9 * u ^ 2 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have h' : 27 * 3 ^ g ∣ 27 * (u ^ 2 * R) := by
    rw [show 27 * 3 ^ g = 3 ^ (g + 2 + 1) by ring, ← mul_assoc]
    exact h
  have h2 : 3 ^ g ∣ u ^ 2 * R := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
  have h3 : 3 ^ g ∣ u ^ 2 := (Nat.Coprime.pow_left g hR).dvd_of_dvd_mul_right h2
  have h4 : 3 ^ g ≤ u ^ 2 := Nat.le_of_dvd (by positivity) h3
  calc 3 ^ (g + 2) = 9 * 3 ^ g := by ring
    _ ≤ 9 * u ^ 2 := Nat.mul_le_mul_left 9 h4

theorem ne_small_of_two_mul {f c : ℕ} (hf : 2 ≤ f) (hX : 2 * c = 3 ^ f * ((3 ^ f) ^ 2 - 1))
    (hc : c = 2520 ∨ c = 95040 ∨ c = 443520 ∨ c = 604800) : False := by
  have hc6 : c ≤ 604800 := by omega
  have hf5 : f < 5 := by
    by_contra h'
    have h : 3 ^ 5 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (not_lt.mp h')
    have h2 : 3 ^ 5 * ((3 ^ 5) ^ 2 - 1) ≤ 3 ^ f * ((3 ^ f) ^ 2 - 1) := by gcongr
    norm_num at h2
    omega
  interval_cases f <;> omega

theorem not_isType429_of_two_mul_card_eq {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {f : ℕ} (hf : 2 ≤ f) (hX : 2 * Nat.card X = 3 ^ f * ((3 ^ f) ^ 2 - 1)) :
    ¬ IsType429 X := by
  have hm9 : 9 ≤ 3 ^ f := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h6 : 6 * Nat.card X = 3 ^ (f + 1) * ((3 ^ f) ^ 2 - 1) := by
    rw [pow_succ]
    linarith
  rintro (⟨p, e, hp, he, h⟩ | h | h | h | h)
  · have hpr : p.Prime := hp.out
    have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hpr.pos
    rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
    ·
      have hc := KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
      have hg : Nat.gcd 3 (p ^ e - 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg] at hc
      obtain ⟨t, ht⟩ : ∃ t, p ^ e = 3 * t + 1 := ⟨p ^ e / 3, by omega⟩
      have ht1 : 1 ≤ t := by
        have : 2 ≤ p ^ e := le_trans hpr.two_le (Nat.le_self_pow (by omega) p)
        omega
      rw [ht] at hc
      have e2 : (3 * t + 1) ^ 2 - 1 = 3 * t * (3 * t + 2) := by
        have : (3 * t + 1) ^ 2 = 3 * t * (3 * t + 2) + 1 := by ring
        omega
      have e3 : (3 * t + 1) ^ 3 - 1 = 9 * t * (3 * t ^ 2 + 3 * t + 1) := by
        have : (3 * t + 1) ^ 3 = 9 * t * (3 * t ^ 2 + 3 * t + 1) + 1 := by ring
        omega
      rw [e2, e3] at hc
      have hR : 3 ^ (f + 1) * ((3 ^ f) ^ 2 - 1) =
          27 * t ^ 2 * (2 * (3 * t + 1) ^ 3 * (3 * t + 2) * (3 * t ^ 2 + 3 * t + 1)) := by
        rw [← h6]
        linear_combination (2 : ℕ) * hc
      have hcop : Nat.Coprime 3 (2 * (3 * t + 1) ^ 3 * (3 * t + 2) * (3 * t ^ 2 + 3 * t + 1)) := by
        refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
        · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
        · exact Nat.Coprime.pow_right 3 (coprime_three_lin le_rfl (by norm_num))
        · exact coprime_three_lin (by norm_num) le_rfl
        · exact coprime_three_quad t
      have hle : 3 ^ f ≤ 9 * t ^ 2 :=
        pow_le_of_dvd hf (by omega) hcop (hR ▸ dvd_mul_right _ _)
      set m := 3 ^ f with hm
      have hlhs : 3 ^ (f + 1) * (m ^ 2 - 1) < 2187 * t ^ 6 := by
        have hm2 : m ^ 2 - 1 < m ^ 2 := by
          have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
          omega
        have hm3 : m ^ 3 ≤ 729 * t ^ 6 := by
          calc m ^ 3 ≤ (9 * t ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
            _ = 729 * t ^ 6 := by ring
        calc 3 ^ (f + 1) * (m ^ 2 - 1) = 3 * m * (m ^ 2 - 1) := by rw [pow_succ, hm]; ring
          _ < 3 * m * m ^ 2 := Nat.mul_lt_mul_of_pos_left hm2 (by omega)
          _ = 3 * m ^ 3 := by ring
          _ ≤ 3 * (729 * t ^ 6) := Nat.mul_le_mul_left 3 hm3
          _ = 2187 * t ^ 6 := by ring
      have hrhs : 2187 * t ^ 6 ≤
          27 * t ^ 2 * (2 * (3 * t + 1) ^ 3 * (3 * t + 2) * (3 * t ^ 2 + 3 * t + 1)) := by
        have a1 : 27 * t ^ 3 ≤ (3 * t + 1) ^ 3 := by
          calc 27 * t ^ 3 = (3 * t) ^ 3 := by ring
            _ ≤ (3 * t + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have a2 : 3 * t ≤ 3 * t + 2 := by omega
        have a3 : 3 * t ^ 2 ≤ 3 * t ^ 2 + 3 * t + 1 := by omega
        have a4 : t ^ 6 ≤ t ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
        calc 2187 * t ^ 6 ≤ 13122 * t ^ 8 := by omega
          _ = 27 * t ^ 2 * (2 * (27 * t ^ 3) * (3 * t) * (3 * t ^ 2)) := by ring
          _ ≤ 27 * t ^ 2 * (2 * (3 * t + 1) ^ 3 * (3 * t + 2) * (3 * t ^ 2 + 3 * t + 1)) := by
            gcongr
      rw [hR] at hlhs
      omega
    ·
      have hc := KS14.card_projSU_three_mul_gcd p e he
      rw [← Nat.card_congr φ.toEquiv] at hc
      have hg : Nat.gcd 3 (p ^ e + 1) = 3 := Nat.gcd_eq_left (by omega)
      rw [hg] at hc
      obtain ⟨t, ht⟩ : ∃ t, p ^ e = 3 * t + 2 := ⟨p ^ e / 3, by omega⟩
      rw [ht] at hc
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      ·
        norm_num at hc
        have : 9 * (9 ^ 2 - 1) ≤ 3 ^ f * ((3 ^ f) ^ 2 - 1) := by gcongr
        omega
      have e2 : (3 * t + 2) ^ 2 - 1 = 3 * (t + 1) * (3 * t + 1) := by
        have : (3 * t + 2) ^ 2 = 3 * (t + 1) * (3 * t + 1) + 1 := by ring
        omega
      have e3 : (3 * t + 2) ^ 3 + 1 = 9 * (t + 1) * (3 * t ^ 2 + 3 * t + 1) := by ring
      rw [e2, e3] at hc
      have hR : 3 ^ (f + 1) * ((3 ^ f) ^ 2 - 1) =
          27 * (t + 1) ^ 2 * (2 * (3 * t + 2) ^ 3 * (3 * t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by
        rw [← h6]
        linear_combination (2 : ℕ) * hc
      have hcop : Nat.Coprime 3 (2 * (3 * t + 2) ^ 3 * (3 * t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by
        refine Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_) ?_
        · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; omega
        · exact Nat.Coprime.pow_right 3 (coprime_three_lin (by norm_num) le_rfl)
        · exact coprime_three_lin le_rfl (by norm_num)
        · exact coprime_three_quad t
      have hle : 3 ^ f ≤ 9 * (t + 1) ^ 2 :=
        pow_le_of_dvd hf (by omega) hcop (hR ▸ dvd_mul_right _ _)
      set m := 3 ^ f with hm
      have hlhs : 32 * (3 ^ (f + 1) * (m ^ 2 - 1)) < 69984 * (t + 1) ^ 6 := by
        have hm2 : m ^ 2 - 1 < m ^ 2 := by
          have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
          omega
        have hm3 : m ^ 3 ≤ 729 * (t + 1) ^ 6 := by
          calc m ^ 3 ≤ (9 * (t + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hle 3
            _ = 729 * (t + 1) ^ 6 := by ring
        calc 32 * (3 ^ (f + 1) * (m ^ 2 - 1)) = 96 * m * (m ^ 2 - 1) := by
              rw [pow_succ, hm]; ring
          _ < 96 * m * m ^ 2 := Nat.mul_lt_mul_of_pos_left hm2 (by omega)
          _ = 96 * m ^ 3 := by ring
          _ ≤ 96 * (729 * (t + 1) ^ 6) := Nat.mul_le_mul_left 96 hm3
          _ = 69984 * (t + 1) ^ 6 := by ring
      have hrhs : 69984 * (t + 1) ^ 6 ≤
          32 * (27 * (t + 1) ^ 2 *
            (2 * (3 * t + 2) ^ 3 * (3 * t + 1) * (3 * t ^ 2 + 3 * t + 1))) := by
        have a1 : 125 * (t + 1) ^ 3 ≤ 8 * (3 * t + 2) ^ 3 := by
          calc 125 * (t + 1) ^ 3 = (5 * (t + 1)) ^ 3 := by ring
            _ ≤ (2 * (3 * t + 2)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
            _ = 8 * (3 * t + 2) ^ 3 := by ring
        have a2 : 2 * (t + 1) ≤ 3 * t + 1 := by omega
        have a3 : 7 * (t + 1) ^ 2 ≤ 4 * (3 * t ^ 2 + 3 * t + 1) := by nlinarith
        have a4 : (t + 1) ^ 6 ≤ (t + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
        calc 69984 * (t + 1) ^ 6 ≤ 94500 * (t + 1) ^ 8 := by omega
          _ = 27 * (t + 1) ^ 2 * (2 * (125 * (t + 1) ^ 3) * (2 * (t + 1)) *
                (7 * (t + 1) ^ 2)) := by ring
          _ ≤ 27 * (t + 1) ^ 2 * (2 * (8 * (3 * t + 2) ^ 3) * (3 * t + 1) *
                (4 * (3 * t ^ 2 + 3 * t + 1))) := by gcongr
          _ = 32 * (27 * (t + 1) ^ 2 *
                (2 * (3 * t + 2) ^ 3 * (3 * t + 1) * (3 * t ^ 2 + 3 * t + 1))) := by ring
      rw [hR] at hlhs
      omega
  · obtain ⟨φ⟩ := h
    exact ne_small_of_two_mul hf
      (((Nat.card_congr φ.toEquiv).trans KS14.card_alternatingGroup_five_seven_ten.2.1) ▸ hX)
      (Or.inl rfl)
  · obtain ⟨φ⟩ := h
    exact ne_small_of_two_mul hf (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeM12) ▸ hX)
      (Or.inr (Or.inl rfl))
  · obtain ⟨φ⟩ := h
    exact ne_small_of_two_mul hf (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeM22) ▸ hX)
      (Or.inr (Or.inr (Or.inl rfl)))
  · obtain ⟨φ⟩ := h
    exact ne_small_of_two_mul hf (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeJ2) ▸ hX)
      (Or.inr (Or.inr (Or.inr rfl)))

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
