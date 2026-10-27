module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoCommon

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_not_sq_dvd_336_mul {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hm : 336 * m ∣ 8709120) : ¬ p ^ 2 ∣ 336 * m := by
  intro h
  have hN : p ^ 2 ∣ 8709120 := h.trans hm
  rw [show (8709120 : ℕ) = 2 ^ 10 * 3 ^ 5 * 5 * 7 by norm_num] at hN
  have hpN : p ∣ 2 ^ 10 * 3 ^ 5 * 5 * 7 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hN
  have hmem : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpN with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · left
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h
    · right; right; right
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at hN
  · norm_num at hN

theorem s168e3_sig_eq_three_of_threeNat_card
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L)) :
    D.sig = {3} := by
  have hdiv : Nat.card ↥(Mbar D.M V₀ V hV) ∣ 336 * Nat.card ↥(lBar V₀ V hV L) :=
    ThreeNat.card_dvd_of_seven hT h7
  have hAeq : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) =
      Nat.card ↥(Mbar D.M V₀ V hV) :=
    c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV
  have h336 : 6 * (56 * Nat.card ↥(lBar V₀ V hV L)) =
      336 * Nat.card ↥(lBar V₀ V hV L) := by ring
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      6 * (56 * Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hAeq, h336]
    exact hdiv
  have harith' : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      ¬ p ^ 2 ∣ 6 * (56 * Nat.card ↥(lBar V₀ V hV L)) := by
    intro p hp hp2 hp3
    rw [h336]
    exact harith p hp hp2 hp3
  exact s168e3_two_sig c hcard harith'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
