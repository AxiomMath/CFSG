module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeAClRA
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRest
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem om6_labelAll_mono {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P)
    (hPP : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → P' R I F) :
    LargeEvenLabelAll lab P' := fun Q hQ =>
  largeEvenRawDatum_mono (fun R _ I F ⟨hq, hp⟩ => ⟨hq, hPP R I F hp⟩) (h Q hQ)

private theorem om6_labelAll_torusLiftFour_twD6 :
    LargeEvenLabelAll ⟨.twD, 6, 1⟩ fun R _ _ _ => GGTorusLift 3 4 R := by
  have h : GGOrthRestLabel 3 (⟨.twD, 6, 1⟩ : LargeEvenLabel) :=
    ⟨by norm_num, Or.inl ⟨rfl, by norm_num⟩⟩
  exact om6_labelAll_mono
    (OrthRest.labelAll ggOrthRestTorusLiftInput_holds Nat.prime_three h)
    fun R _ _ _ hP => ggTorusLift_mono Nat.prime_three hP.2 (by norm_num)

theorem ggTwoLocalRank_D5_two_three
    {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) (hX : GGHasLabel ⟨.D, 5, 1⟩ (X ⧸ Subgroup.center X)) :
    4 ≤ LargeEvenTwoLocalRank 3 X := by
  have hraw : LargeEvenRawDatum (⟨.D, 5, 1⟩ : LargeEvenLabel)
      (fun R' _ _ _ => Nonempty ((X ⧸ Subgroup.center X) ≃* R')) := hX
  dsimp only [LargeEvenRawDatum] at hraw
  rw [if_neg (by norm_num : ¬ (5 : ℕ) = 3)] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, hNon⟩ := hraw
  have hK2 : Nat.card K = 2 := by rw [hKcard, pow_one]
  obtain ⟨e⟩ := hNon
  have hT : GGTorusLift 3 4 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 5))) :=
    ggOrthRestTorusLiftInput_holds.2 K 5 hK2 (by norm_num)
  exact tara_le_twoLocalRank_of_torusLift Nat.prime_three hT e hperf

theorem ggTwoLocalRank_twD6_two_three
    {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) (hX : GGHasLabel ⟨.twD, 6, 1⟩ (X ⧸ Subgroup.center X)) :
    4 ≤ LargeEvenTwoLocalRank 3 X := by
  have hAll := om6_labelAll_torusLiftFour_twD6
  have hRaw := hAll (fun R _ _ _ => Nonempty (X ⧸ Subgroup.center X ≃* R)) hX
  obtain ⟨R, hR, I, F, ⟨⟨e⟩, hT⟩⟩ := largeEvenRawDatum_exists hRaw
  letI := hR
  exact tara_le_twoLocalRank_of_torusLift Nat.prime_three hT e hperf

end CFSG.StandardType

end
