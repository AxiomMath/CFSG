module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_big_ceiling_factor :
    (935911159612047360 : ℕ) = 2 ^ 25 * 3 ^ 5 * 5 * 7 ^ 3 * 17 * 31 * 127 := by
  norm_num

private theorem s168e3_prime_dvd_big_ceiling_cases {p : ℕ} (hp : p.Prime)
    (h : p ∣ 935911159612047360) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  rw [s168e3_big_ceiling_factor] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h127
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h31
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h17
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h3
            · left
              exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
            · right; left
              exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
          · right; right; left
            exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
        · right; right; right; left
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 (hp.dvd_of_dvd_pow h7)
      · right; right; right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 h17
    · right; right; right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).1 h31
  · right; right; right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)).1 h127

theorem s168e3_prime_eq_three_or_seven_of_sq_dvd_336_mul
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsq : p ^ 2 ∣ 336 * m) (hm : 336 * m ∣ 935911159612047360) :
    p = 3 ∨ p = 7 := by
  have hN : p ^ 2 ∣ 935911159612047360 := hsq.trans hm
  have hpC : p ∣ 935911159612047360 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hN
  rcases s168e3_prime_dvd_big_ceiling_cases hp hpC with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · norm_num at hN
  · exact Or.inr rfl
  · norm_num at hN
  · norm_num at hN
  · norm_num at hN

theorem s168e3_card_statedSL_six_seven_dvd {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    336 * Nat.card (StatedSL n K) ∣ 935911159612047360 := by
  rcases hn with rfl | rfl
  · rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 6) (by norm_num), hK]
    decide
  · rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 7) (by norm_num), hK]
    decide

theorem s168e3_sq_dvd_336_of_mem_sig
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {p : ℕ} (hp : p ∈ D.sig) :
    p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := by
  have hAeq : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) =
      Nat.card ↥(Mbar D.M V₀ V hV) :=
    c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV
  have hsqA : p ^ 2 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    rw [← hAeq]
    exact s168e3_two_pow_dvd_card c hp
  exact hsqA.trans (ThreeNat.card_dvd_of_seven hT h7)

theorem s168e3_kBar_card_seven_of_three_not_dvd
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (h3 : ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) :
    Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7 := by
  obtain ⟨-, -, -, -, -, -, -, hcase⟩ := hT.structure_of_seven h7
  rcases hcase with hK | hK | ⟨hK, -⟩
  · exact hK
  · exact absurd (by rw [hK]; norm_num : 3 ∣
      Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) h3
  · exact absurd (by rw [hK]; norm_num : 3 ∣
      Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
