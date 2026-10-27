module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA6
public import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofExc
import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofL3
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.Open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint

section Kills

variable {X : Type} [Group X] [Finite X] {P : Subgroup X}

theorem false_of_five_not_dvd {M : Type} [Group M] (e : X ≃* M) (hM : ¬ 5 ∣ Nat.card M)
    (hP : IsA6Sub P) : False := by
  apply hM
  rw [← Nat.card_congr e.toEquiv]
  exact hP.five_dvd_card

theorem false_of_three_not_dvd {M : Type} [Group M] (e : X ≃* M) (hM : ¬ 3 ∣ Nat.card M)
    (hP : IsA6Sub P) : False := by
  apply hM
  rw [← Nat.card_congr e.toEquiv]
  exact hP.three_dvd_card

theorem false_of_suzuki {n : ℕ} (h : SuzukiModel X 2 n)
    (hP : IsA6Sub P) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine false_of_three_not_dvd e ?_ hP
  exact KFacts.not_three_dvd_card_suzukiGroup (by rw [hK, hf])

theorem false_of_statedSU_odd {m : ℕ} (hm : Odd m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ m) ^ 2) (φ : X ≃* StatedSU 3 (2 ^ m) K) (hP : IsA6Sub P) :
    False := by
  refine false_of_five_not_dvd φ ?_ hP
  rw [Sec8.Item87Proof.card_statedSU_three_two hK]
  intro h
  obtain ⟨h0, h2, -, h3⟩ := Sec21.Item228Census2Proof.not_five_dvd_factors
    (SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_five hm)
  have h' : 5 ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) := by
    rwa [show (2 : ℕ) ^ (3 * m) = (2 ^ m) ^ 3 by rw [pow_mul']] at h
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h' with h | h
  · exact h0 (Nat.prime_five.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
    · exact h2 h
    · exact h3 h

theorem false_of_projSU_odd {m : ℕ} (hm : Odd m) (φ : X ≃* projSU 3 2 m) (hP : IsA6Sub P) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by have := hm.pos; omega), ← pow_mul, mul_comm]
  exact false_of_five_not_dvd (φ.trans (PGLModel.projSUEquivStatedProj 3 2 m))
    (Sec21.Item228Census2Proof.not_five_dvd_card_statedProj_statedSU_three' Nat.prime_two hm.pos
      hK (SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_five hm)) hP


theorem false_of_g2 {n : ℕ} (hn : Odd n) (h : ChevalleyExceptionalModel X .G2 2 n)
    (hP : IsA6Sub P) : False := by
  refine false_of_five_not_dvd (M := X) (MulEquiv.refl X) ?_ hP
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional h]
  exact Sec21.Item228Census2Proof.not_five_dvd_ordG2 hn

theorem false_of_d4 {n : ℕ} (hn : Odd n) (h : ChevalleyExceptionalModel X .trialityD4 2 n)
    (hP : IsA6Sub P) : False := by
  refine false_of_five_not_dvd (M := X) (MulEquiv.refl X) ?_ hP
  rw [EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional h]
  exact Sec21.Item228Census2Proof.not_five_dvd_ordTrialityD4 hn

theorem false_of_projSL3 {n : ℕ} (hn : Odd n) (φ : X ≃* projSL 3 (GaloisField 2 n))
    (hP : IsA6Sub P) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.pos.ne'
  exact false_of_five_not_dvd (φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n)))
    (Sec21.Item228Census2Proof.not_five_dvd_card_projectiveSL_three
      (by rw [hK]; exact SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_five hn)) hP

end Kills

end CFSG.RankThree.PartTwo.Sec8.Hering611R
