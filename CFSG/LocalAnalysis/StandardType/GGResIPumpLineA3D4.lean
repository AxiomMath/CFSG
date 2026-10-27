module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_D4_notDvdSCJ
    (n : ℕ)
    (hn : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) (labJ : LargeEvenLabel) :
    LargeEvenLabelAll ⟨.D, 4, n⟩ fun R _ I _ => GGTorusAutNotDvdSCJ 3 labJ R I 4 27 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by norm_num : (4 : ℕ) ≠ 3)] at hQ
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hQ
  refine ⟨K, hKfield, hKfinite, hKcard, hQ, ?_⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 _ hsc _
  have hchar : CharP K 2 := CFSG.StandardType.charP_two_of_card hKcard
  have hcond : 3 ∣ Nat.card K - 1 ∨ (Even 4 ∧ 3 ∣ Nat.card K + 1) := by
    rw [hKcard]
    rcases hn with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by norm_num, h⟩
  have hT : GGTorusEvenSignedPermEltSC 3 (OrthRest.RPlus K 4) (fun k => k = 4) :=
    ggOrthEvenTorusInput_holds.1 K 4 3 (by norm_num) Nat.prime_three hcond
  obtain ⟨hZ, hcp⟩ :=
    OrthNs.center_data_omegaPlus (K := K) (m := 4) (p := 3) Nat.prime_three (by norm_num) (by norm_num)
  obtain ⟨k, Θ, -, hk4, -, -, -, -, hsp⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC (p := 3) (R := OrthRest.RPlus K 4)
      (kP := fun k => k = 4) Nat.prime_three (by norm_num) (fun _ h => h) hZ hcp hT
        hψ hker hperf hA hAI h3 hsc
  subst k
  have hdvd := SignedPermCount.card_dvd_signed_of_normalizer_model
    (p := 3) (k := 4) Nat.prime_three (by norm_num) (A := A) Θ hsp
  rw [show 2 ^ 4 * Nat.factorial 4 = 384 by norm_num] at hdvd
  intro hbad
  exact (by norm_num : ¬ 27 ∣ 384) (hbad.trans hdvd)

end CFSG.StandardType

end
