module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankAny
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_eq_two_of_lieModel_G2_odd
    {p f : ℕ} (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : LieModel X .G2 0 p f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hX : ChevalleyExceptionalModel X .G2 p f := h.chevalleyExceptionalModel (by decide)
  obtain ⟨K, hKfield, hKfin, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hX.2
  letI := hKfield
  letI := hKfin
  have hp : p.Prime := hX.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hX.1.2.1
  have hK' : Nat.card K = p ^ f := hK
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK']
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.not_three_dvd_prime_pow hp hp3 f
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eZ : adjointGroup .G2 K ≃* AdjointQuotient .G2 K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hlowQuot : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient .G2 K)) :=
    CFSG.LieType.Chevalley.two_le_pRank_three_adjointQuotient_G2
  have hlowAdj : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .G2 K)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eZ]
    exact hlowQuot
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    exact hlowAdj
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) (fun F _ hF => ?_)
    letI : Fintype K := Fintype.ofFinite K
    have hchar : CharP K p :=
      charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK'])
    haveI : CharP K p := hchar
    have hk2 : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      exact hp2
    have hk3 : (3 : K) ≠ 0 :=
      CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card hp hp3 hK'
    have h9 := CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.adjointG2_card_le_nine
      (k := K) hk2 hk3 F hF
    simpa using h9
  exact le_antisymm hupper hlow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
