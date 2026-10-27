module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofTools
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item228Census2Proof

theorem not_five_dvd_ordG2 {f : ℕ} (hf : Odd f) : ¬ 5 ∣ CFSG.Open.ordG2 (2 ^ f) := by
  have h2 := two_pow_sq_mod_five hf
  have h6 : (2 ^ f) ^ 6 % 5 = 4 := by
    rw [show (2 ^ f) ^ 6 = ((2 ^ f) ^ 2) ^ 3 by ring, Nat.pow_mod, h2]
  unfold CFSG.Open.ordG2
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · exact not_five_dvd_two_pow_pow f 6 h
    · generalize (2 ^ f) ^ 6 = Q at h h6
      omega
  · generalize (2 ^ f) ^ 2 = Q at h h2
    omega

theorem not_five_dvd_ordTrialityD4 {f : ℕ} (hf : Odd f) :
    ¬ 5 ∣ CFSG.Open.ordTrialityD4 (2 ^ f) := by
  have h2 := two_pow_sq_mod_five hf
  have h4 : (2 ^ f) ^ 4 % 5 = 1 := by
    rw [show (2 ^ f) ^ 4 = ((2 ^ f) ^ 2) ^ 2 by ring, Nat.pow_mod, h2]
  have h6 : (2 ^ f) ^ 6 % 5 = 4 := by
    rw [show (2 ^ f) ^ 6 = ((2 ^ f) ^ 2) ^ 3 by ring, Nat.pow_mod, h2]
  have h8 : (2 ^ f) ^ 8 % 5 = 1 := by
    rw [show (2 ^ f) ^ 8 = ((2 ^ f) ^ 2) ^ 4 by ring, Nat.pow_mod, h2]
  unfold CFSG.Open.ordTrialityD4
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
      · exact not_five_dvd_two_pow_pow f 12 h
      · generalize (2 ^ f) ^ 8 = Q8 at h h8
        generalize (2 ^ f) ^ 4 = Q4 at h h4
        omega
    · generalize (2 ^ f) ^ 6 = Q at h h6
      omega
  · generalize (2 ^ f) ^ 2 = Q at h h2
    omega

theorem noL2Normal228_of_not_five_dvd {S : Type} [Group S] [Finite S]
    (h5 : ¬ 5 ∣ Nat.card S) : NoL2Normal228 S := by
  intro y N Kb m _ _ _ _ _ ⟨eK⟩ hm he _
  apply h5
  have h : 5 ∣ Nat.card Kb := by
    rw [Nat.card_congr eK.toEquiv]
    exact Item22Res4Proof.five_dvd_card_projSL_two hm he
  exact h.trans (Subgroup.card_subgroup_dvd_card Kb)

end Item228Census2Proof

open Item228Census2Proof


theorem census228G2TwoOdd_holds : Census228G2TwoOdd := by
  intro Y _ _ ⟨f, hf, hY⟩
  have hcard : Nat.card Y = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hY
  exact Or.inr (noL2Normal228_of_not_five_dvd (hcard ▸ not_five_dvd_ordG2 hf))

theorem census228D4TwoOdd_holds : Census228D4TwoOdd := by
  intro Y _ _ ⟨f, hf, hY⟩
  have hcard : Nat.card Y = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hY
  exact Or.inr (noL2Normal228_of_not_five_dvd (hcard ▸ not_five_dvd_ordTrialityD4 hf))

end CFSG.RankThree.PartTwo.Sec21
