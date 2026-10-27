module

public import CFSG.Models.PGLSimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_eight_simple_of_isSLn_two_three {X : Type} [Group X] [Finite X]
    (h : IsSLn X 2 3) : IsSimpleGroup X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    norm_num
  have hchar : ringChar K = 2 := (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 2) (by norm_num)
      (Or.inr hK2) (Or.inr hK3)
  haveI : IsSimpleGroup ↥(StatedSL 2 K) := q.symm.isSimpleGroup
  exact e.isSimpleGroup

theorem s16h_sl28_eight_seven_dvd_card_of_isSLn_two_three {X : Type} [Group X]
    (h : IsSLn X 2 3) : 7 ∣ Nat.card X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKcard]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
