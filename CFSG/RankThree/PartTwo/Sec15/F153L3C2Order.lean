module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem two_pow_dvd_card_projSL {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (3 * f) ∣ Nat.card (projSL 3 (GaloisField 2 f)) := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
  rw [GaloisField.card 2 f (by omega)] at h
  have h23 : Nat.Coprime 2 3 := by norm_num
  have hcop : Nat.Coprime (2 ^ (3 * f)) (Nat.gcd 3 (2 ^ f - 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) h23)
  apply hcop.dvd_of_dvd_mul_right
  rw [h]
  exact Dvd.dvd.mul_right (dvd_of_eq (by ring)) _

theorem two_pow_dvd_card_projSU {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (3 * f) ∣ Nat.card (projSU 3 2 f) := by
  have h := KFacts.KS14.card_projSU_three_mul_gcd 2 f hf
  have h23 : Nat.Coprime 2 3 := by norm_num
  have hcop : Nat.Coprime (2 ^ (3 * f)) (Nat.gcd 3 (2 ^ f + 1)) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _) h23)
  apply hcop.dvd_of_dvd_mul_right
  rw [h]
  exact Dvd.dvd.mul_right (dvd_of_eq (by ring)) _

theorem order_of_isLThreeEpsAt {T : Type} [Group T] {f : ℕ} (hf : 1 ≤ f)
    (hL : Sec14.IsLThreeEpsAt T 2 f) :
    2 ^ (3 * f) ∣ Nat.card T ∧
      (Nat.card T * Nat.gcd 3 (2 ^ f - 1) =
          (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) ∨
        (2 < 2 ^ f ∧ Nat.card T * Nat.gcd 3 (2 ^ f + 1) =
          (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)))) := by
  rcases hL with ⟨⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
    rw [GaloisField.card 2 f (by omega)] at h
    exact ⟨two_pow_dvd_card_projSL hf, Or.inl h⟩
  · rw [Nat.card_congr e.toEquiv]
    exact ⟨two_pow_dvd_card_projSU hf, Or.inr ⟨hq, KFacts.KS14.card_projSU_three_mul_gcd 2 f hf⟩⟩

theorem f_le_of_two_pow_dvd {N f k : ℕ} (h : 2 ^ (3 * f) ∣ N)
    (hk : ¬ 2 ^ (3 * (k + 1)) ∣ N) : f ≤ k := by
  by_contra hfk
  exact hk ((pow_dvd_pow 2 (by omega : 3 * (k + 1) ≤ 3 * f)).trans h)

theorem kL3Char2NotList148_holds : KL3Char2NotList148 := by
  intro T _ f hf hL
  obtain ⟨hdiv, hord⟩ := order_of_isLThreeEpsAt hf hL
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩,
    ⟨fun e => ?_⟩, fun hp7 => ⟨fun e => ?_⟩⟩
  ·
    have hN : Nat.card T = 60 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
    rw [hN] at hdiv
    have h8 := (pow_dvd_pow 2 (by omega : 3 ≤ 3 * f)).trans hdiv
    norm_num at h8
  ·
    have hN : Nat.card T = 360 := by
      rw [Nat.card_congr e.toEquiv,
        KFacts.KS14.card_alternatingGroup_fin (n := 6) (by norm_num)]
      decide
    rw [hN] at hdiv hord
    have hf1 := f_le_of_two_pow_dvd (k := 1) hdiv (by norm_num)
    obtain rfl : f = 1 := by omega
    norm_num at hord
  ·
    have hN : Nat.card T = 2520 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
    rw [hN] at hdiv hord
    have hf1 := f_le_of_two_pow_dvd (k := 1) hdiv (by norm_num)
    obtain rfl : f = 1 := by omega
    norm_num at hord
  ·
    have hN : Nat.card T = 1814400 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
    rw [hN] at hdiv hord
    have hf2 := f_le_of_two_pow_dvd (k := 2) hdiv (by norm_num)
    interval_cases f <;> norm_num at hord
  ·
    have hN : Nat.card T = 460815505920 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON]
    rw [hN] at hdiv hord
    have hf3 := f_le_of_two_pow_dvd (k := 3) hdiv (by norm_num)
    interval_cases f <;> norm_num at hord
  ·
    have hN : Nat.card T = 604800 := by
      rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
    rw [hN] at hdiv hord
    have hf2 := f_le_of_two_pow_dvd (k := 2) hdiv (by norm_num)
    interval_cases f <;> norm_num at hord
  ·
    have h7 : Nat.card (projSL 3 (GaloisField 7 1)) = 1876896 := by
      have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
      rw [GaloisField.card 7 1 (by norm_num)] at h
      norm_num at h
      omega
    have hN : Nat.card T = 1876896 := by
      rw [Nat.card_congr e.toEquiv, h7]
    rw [hN] at hdiv hord
    have hf1 := f_le_of_two_pow_dvd (k := 1) hdiv (by norm_num)
    interval_cases f
    norm_num at hord

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
