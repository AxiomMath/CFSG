module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofRee

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly (IsElemAbelian)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSU StatedProj StatedScalars)

namespace Item228Census2Proof

theorem not_five_dvd_factors {q : ℕ} (hq : q % 5 = 2 ∨ q % 5 = 3) :
    ¬ 5 ∣ q ∧ ¬ 5 ∣ q ^ 2 - 1 ∧ ¬ 5 ∣ q ^ 3 - 1 ∧ ¬ 5 ∣ q ^ 3 + 1 := by
  have h2 : q ^ 2 % 5 = (q % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
  have h3 : q ^ 3 % 5 = (q % 5) ^ 3 % 5 := Nat.pow_mod _ _ _
  have hq1 : 1 ≤ q := by omega
  have h21 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h31 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  rcases hq with hq | hq <;> rw [hq] at h2 h3 <;> norm_num at h2 h3 <;>
    refine ⟨by omega, ?_, ?_, ?_⟩ <;>
    · generalize q ^ 2 = Q2 at *
      generalize q ^ 3 = Q3 at *
      omega

theorem not_five_dvd_card_SL_three {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 5 = 2 ∨ Nat.card K % 5 = 3) :
    ¬ 5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := 3) (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  obtain ⟨h0, h2, h3, -⟩ := not_five_dvd_factors hq
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
  · exact h0 (Nat.prime_five.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · exact h2 h
    · exact h3 h

theorem not_five_dvd_card_projectiveSL_three {K : Type} [Field K] [Finite K]
    (hq : Nat.card K % 5 = 2 ∨ Nat.card K % 5 = 3) :
    ¬ 5 ∣ Nat.card (projectiveSL 3 K) := fun h5 =>
  not_five_dvd_card_SL_three hq (h5.trans (Dvd.intro _
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 K)).symm))

theorem not_five_dvd_card_statedProj_statedSU_three' {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 5 = 2 ∨ p ^ f % 5 = 3) :
    ¬ 5 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have hP := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hp hf hK
    (by norm_num)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  rw [prod_Icc_two_three_unitary _ hq1] at hP
  rw [hP]
  set q := p ^ f
  obtain ⟨h0, h2, -, h3⟩ := not_five_dvd_factors hq
  have hd : Nat.gcd 3 (q + 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    refine (Nat.gcd_dvd_right 3 (q + 1)).trans (Dvd.dvd.mul_left ?_ _)
    refine Dvd.dvd.mul_left ?_ _
    exact ⟨q ^ 2 - q + 1, by
      have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      zify [this, hq1]
      ring⟩
  intro h5
  have h5' : 5 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rw [← Nat.div_mul_cancel hd]
    exact Dvd.dvd.mul_right h5 _
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5' with h | h
  · exact h0 (Nat.prime_five.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · exact h2 h
    · exact h3 h

end Item228Census2Proof

open Item228Census2Proof

end CFSG.RankThree.PartTwo.Sec21
