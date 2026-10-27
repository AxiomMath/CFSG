module

public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.RankThree.GF2n.Smith81.TiRecognition
public import CFSG.Timmesfeld.CorollaryBOutcome
public import CFSG.Timmesfeld.CorollaryBQuot

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders

theorem factorization_ordA_two {f : ℕ} (hf : 1 ≤ f) :
    (ordA 2 (2 ^ f)).factorization 2 = 3 * f := by
  set q := 2 ^ f with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : Odd (q ^ 2 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 2) hf (by norm_num)
  have h3 : Odd (q ^ 3 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 3) hf (by norm_num)
  have hP : Odd ((q ^ 2 - 1) * (q ^ 3 - 1)) := h2.mul h3
  have hg : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    refine Dvd.dvd.mul_right ?_ _
    exact (Nat.gcd_dvd_right 3 (q - 1)).trans (Nat.sub_one_dvd_pow_sub_one q 2)
  have hgodd : Odd (Nat.gcd 3 (q - 1)) := by
    have : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := hg
    exact Odd.of_dvd_nat hP this
  have hA : ordA 2 q = 2 ^ (3 * f) * (((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)) := by
    unfold ordA
    rw [show 2 * (2 + 1) / 2 = 3 by norm_num, show Finset.Icc 2 (2 + 1) = {2, 3} by decide,
      Finset.prod_pair (by norm_num), ← Nat.mul_div_assoc _ hg, hq, ← pow_mul, mul_comm f 3]
  rw [hA]
  refine factorization_two_eq_of_odd rfl ?_
  have : ((q ^ 2 - 1) * (q ^ 3 - 1)) = Nat.gcd 3 (q - 1) *
      (((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)) := (Nat.mul_div_cancel' hg).symm
  rw [this] at hP
  exact (Nat.odd_mul.mp hP).2

theorem factorization_ordG2_two {f : ℕ} (hf : 1 ≤ f) :
    (ordG2 (2 ^ f)).factorization 2 = 6 * f := by
  set q := 2 ^ f with hq
  have h6 : Odd (q ^ 6 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 6) hf (by norm_num)
  have h2 : Odd (q ^ 2 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 2) hf (by norm_num)
  refine factorization_two_eq_of_odd (m := (q ^ 6 - 1) * (q ^ 2 - 1)) ?_ (h6.mul h2)
  unfold ordG2
  rw [hq, ← pow_mul, mul_comm f 6]
  ring

theorem factorization_ordTrialityD4_two {f : ℕ} (hf : 1 ≤ f) :
    (ordTrialityD4 (2 ^ f)).factorization 2 = 12 * f := by
  set q := 2 ^ f with hq
  have h6 : Odd (q ^ 6 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 6) hf (by norm_num)
  have h2 : Odd (q ^ 2 - 1) := by
    simpa [hq] using odd_two_pow_pow_sub_one (f := f) (n := 2) hf (by norm_num)
  have h8 : Odd (q ^ 8 + q ^ 4 + 1) := by
    have e8 : 2 ∣ q ^ 8 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have e4 : 2 ∣ q ^ 4 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    rw [Nat.odd_iff]
    omega
  refine factorization_two_eq_of_odd (m := (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)))
    ?_ (h8.mul (h6.mul h2))
  unfold ordTrialityD4
  rw [hq, ← pow_mul, mul_comm f 12]
  ring

theorem factorization_psu_three_three {Y : Type} [Group Y]
    (hL : CFSG.Blueprint.LieModel Y .PSU 3 3 1) : (Nat.card Y).factorization 2 = 5 := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have hcard := card_psu_three_mul_gcd (K := K) Nat.prime_three hf (by simpa using hK)
  rw [Nat.card_congr e.toEquiv]
  have hg : Nat.gcd 3 (3 ^ 1 + 1) = 1 := by norm_num
  rw [hg, mul_one] at hcard
  exact factorization_two_eq_of_odd (k := 5) (m := 189) (by rw [hcard]; norm_num) (by decide)

theorem tiLieOrders_holds : TiLieOrders := by
  refine ⟨?_, ?_, ?_, fun Y _ hL => factorization_psu_three_three hL⟩
  · intro Y _ f hL
    have hf := hL.admissible.2.1
    have h := hL.statedClassicalModel_of_ne_zero (by norm_num)
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    rw [hc]
    exact factorization_ordA_two hf
  · intro Y _ f hL
    have hf := hL.admissible.2.1
    have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (hL.chevalleyExceptionalModel (by decide))
    rw [hc]
    exact factorization_ordG2_two hf
  · intro Y _ f hL
    have hf := hL.admissible.2.1
    have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (hL.chevalleyExceptionalModel (by decide))
    rw [hc]
    exact factorization_ordTrialityD4_two hf

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem corBRankTwo_holds : CorBRankTwo := by
  intro X _ _ t hS hpair h4 hlarge
  have hH := hS.hyp_quotient hpair h4
  have hno := hS.noOddCent_quotient h4
  have hNO := CFSG.Timmesfeld.CorB.noOppCentral_rootClass hH.root hno
  obtain ⟨hc, hs, hm, -⟩ := CFSG.Timmesfeld.CorB.largeFacts hH hlarge
  have hARS := CFSG.Timmesfeld.CorB.outcomeTwo_of_noOppCentral
    (CFSG.Timmesfeld.arsHyp_rootClass hH hc hs hm) hNO
  rcases hARS with ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ | ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ |
      ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ | hU
  · exact Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩))
  · exact Or.inr (Or.inr (Or.inr hU))

end CFSG.RankThree.GF2n.Smith81
