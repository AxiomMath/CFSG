module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2LieOfType
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33ExceptionalRanks
import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
import CFSG.Quasithin.Background.A318PL3Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Blueprint CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartTwo.Census.Carrier.Tits (card_reeFixed pRank_three_reeFixed)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 (pRank_three_eq_two_of_lieModel_trialityD4)

private theorem pRank_three_le_two_of_reeTitsModel_tits
    {S : Type} [Group S] [Finite S]
    (h : ReeTitsModel S .Tits 2 1) : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 2 := by
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model h
  have : Finite (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 F 0) :=
    Nat.finite_of_card_ne_zero (by rw [card_reeFixed hF]; norm_num)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) (commutator _).subtype
    Subtype.val_injective).trans (pRank_three_reeFixed hF)

private noncomputable def mulEquivQuotientCenter {K : Type} [Group K]
    (hZ : Subgroup.center K = ⊥) : K ≃* K ⧸ Subgroup.center K :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

private theorem gf2PermType_of_two_lt_pRank
    (hN : uc22p20rNativeGriess) {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hodd : Odd (Nat.card (Subgroup.center K))) {t : CFSG.Open.StatedLieTag} {m : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t m 2 1) (hL : LieModel (K ⧸ Subgroup.center K) t m 2 1)
    (h3 : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    Inputs1719.GF2PermType t m := by
  have hK (hg : genericOrders t m 2 1 = (1, 1)) : LieModel K t m 2 1 :=
    LieModel.of_mulEquiv (mulEquivQuotientCenter (uc22p20v_center_eq_bot hN hq hodd hL hg)).symm
      hL
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
  · obtain ⟨rfl, hm⟩ := ht
    obtain ⟨-, -, hm2, hm22, -⟩ := hadm
    obtain rfl : m = 3 := by
      interval_cases m
      · simp at hm22
      · rfl
    have := CFSG.Quasithin.A318P.pRank_three_le_one_linear
      ((hK rfl).statedClassicalModel (by decide)) (by norm_num)
    omega
  · subst ht
    obtain ⟨-, -, rfl⟩ := hadm
    have := pRank_three_eq_two_of_lieModel_trialityD4 (hK rfl)
    omega
  · subst ht
    have := pRank_three_le_two_of_reeTitsModel_tits ((hK rfl).reeTitsModel (by decide)).2
    omega

theorem k_GF2_permutability_of_ofType
    (hN : uc22p20rNativeGriess)
    (h : Inputs1719.K_GF2_permutabilityOfType) : Inputs1719.K_GF2_permutability := by
  rintro Y _ _ K hK hq hodd ⟨t, m, hadm, hL⟩ h3 - - S hS
  rcases h3 with h3 | hL5
  · exact h Y K hK hodd t m hadm (gf2PermType_of_two_lt_pRank hN hq hodd hadm hL h3) hL S hS
  · exact h Y K hK hodd .PSL 5 ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ hL5 S hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
