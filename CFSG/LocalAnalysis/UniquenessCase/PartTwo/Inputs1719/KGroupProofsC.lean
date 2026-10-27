module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kOmega6MinusU4_holds : KOmega6MinusU4 := by
  intro X _ n K _ _ b c hcard hirr hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard, h0, pow_zero] at h1
    exact lt_irrefl 1 h1
  haveI : CharP K 2 :=
    CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := n) hcard
  obtain ⟨E, hEfield, hEU, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      (m := n) hcard hirr
  letI : Field E := hEfield
  letI : Finite E := hEU.finite
  haveI : CharP E 2 := hEU.charP
  have hEcard : Nat.card E = (2 ^ n) ^ 2 := by
    rw [hEU.card, ← pow_mul, Nat.mul_comm]
  have hΩbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b c)) = ⊥ := by
    refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
      (Q₀ := StatedQuadMinus 3 K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) ?_
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) (1 : K), ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    norm_num
  have hSUbot : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ n) E) = ⊥ :=
    CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := n) hEcard
  obtain ⟨eX⟩ := hX
  have eAll : X ≃* StatedProj (StatedSU 4 (2 ^ n) E) :=
    eX.trans ((CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot
      (StatedOmega (StatedQuadMinus 3 K b c)) hΩbot).symm.trans
      (eSU.trans (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot
        (StatedSU 4 (2 ^ n) E) hSUbot)))
  have hnq : (4, 2 ^ n) ≠ (3, 2) := by
    intro h
    exact absurd (congrArg Prod.fst h) (by norm_num)
  refine Or.inl ⟨by decide, ⟨⟨Nat.prime_two, hn1, by norm_num, hnq⟩, E, hEfield,
    hEU.finite, hEcard, ⟨eAll⟩⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
