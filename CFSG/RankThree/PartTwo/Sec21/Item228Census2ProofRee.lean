module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofTools
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofRee
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedSU StatedScalars StatedProj)

open CFSG.LieType.Ree

namespace Item228Census2Proof

theorem prod_Icc_two_three_unitary (q : ℕ) (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 2 3, (((q : ℤ)) ^ i - (-1) ^ i).toNat = (q ^ 2 - 1) * (q ^ 3 + 1) := by
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have e2 : (((q : ℤ)) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    rw [show ((q : ℤ)) ^ 2 - (-1) ^ 2 = ((q ^ 2 - 1 : ℕ) : ℤ) by push_cast [h2]; ring]
    exact Int.toNat_natCast _
  have e3 : (((q : ℤ)) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℤ)) ^ 3 - (-1) ^ 3 = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [e2, e3]

theorem not_five_dvd_card_statedProj_statedSU_three {a : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ (2 * a + 1)) ^ 2) :
    ¬ 5 ∣ Nat.card (StatedProj (StatedSU 3 (2 ^ (2 * a + 1)) K)) := by
  have hP := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (p := 2)
    (f := 2 * a + 1) (n := 3) Nat.prime_two (by omega) hK (by norm_num)
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  rw [prod_Icc_two_three_unitary _ hq1] at hP
  rw [hP]
  set q := 2 ^ (2 * a + 1) with hq
  have h2 : q ^ 2 % 5 = 4 := two_pow_sq_mod_five (odd_two_mul_add_one a)
  have hq5 : q % 5 = 2 ∨ q % 5 = 3 := by
    have : q ^ 2 % 5 = (q % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
    have hlt : q % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : q % 5 <;> simp_all
  have h3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rw [show q ^ 3 = q ^ 2 * q by ring, Nat.mul_mod, h2]
    rcases hq5 with h | h <;> rw [h] <;> norm_num
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
  · exact not_five_dvd_two_pow_pow _ 3 h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · generalize q ^ 2 = Q at h h2
      omega
    · generalize q ^ 3 = Q at h h3
      omega

theorem not_five_dvd_card_statedSU_three {a : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ (2 * a + 1)) ^ 2) :
    ¬ 5 ∣ Nat.card (StatedSU 3 (2 ^ (2 * a + 1)) K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ (2 * a + 1)) K))
  have hZ5 : ¬ 5 ∣ Nat.card
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ (2 * a + 1)) K)) := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hzmem : ((z : StatedSU 3 (2 ^ (2 * a + 1)) K) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K := Subgroup.mem_subgroupOf.mp z.2
    obtain ⟨c, hc⟩ := hzmem
    have hcS : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 (2 ^ (2 * a + 1)) K := by
      rw [hc]
      exact (z : StatedSU 3 (2 ^ (2 * a + 1)) K).2
    have hc3 := ((CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK (by norm_num)
      c).mp hcS).1
    have hz3 : z ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hc, ← map_pow, hc3, map_one]
    have := orderOf_dvd_of_pow_eq_one hz3
    rw [hz] at this
    norm_num at this
  intro h5
  rw [hcard] at h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5 with h | h
  · exact not_five_dvd_card_statedProj_statedSU_three hK h
  · exact hZ5 h

end Item228Census2Proof

open Item228Census2Proof


theorem census228Ree2F4_of (hC : Sec8.KF83ReeCentThree) : Census228Ree2F4 := by
  intro Y _ _ ⟨f, hY⟩
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := CFSG.RankThree.PartOne.KEXC.exists_gamma_of_model hY
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have : Finite (ReeTag.F4.reeGamma K a) := Finite.of_equiv _ e.toEquiv
  refine Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv e
    (noL2Normal228_of_perfectResidual (ReeTag.large_Ree_fixed_group_center_trivial a K hK')
      fun y hy => ?_))
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := hC a K ha hK' y hy
  rw [Nat.card_congr eS.toEquiv]
  exact not_five_dvd_card_statedSU_three hF

end CFSG.RankThree.PartTwo.Sec21
