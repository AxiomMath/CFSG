module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K46Core
public import CFSG.LocalAnalysis.UniquenessCase.UC6K46Mult
public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46Quasi
public import CFSG.LocalAnalysis.UniquenessCase.UC1K32
public import CFSG.LocalAnalysis.UniquenessCase.UC6KSzHolds
public import CFSG.Blueprint.LieModelAPI
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSporThree
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.FFModules (fixSub)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.CGT.PushingUpLit.CGT6 (SporadicThreeCenterSmallPrimes)

theorem k46List_of_inputs (hSz : KSz) (hK32 : K32) (hGA : GriessMultipliersAllModels)
    (hSp : SporadicThreeCenterSmallPrimes) : K46List := by
  intro G _ _ hK V _ _ _ ρ hρ hirr D hD hgen hfix h3 hperf
  haveI : ρ.IsIrreducible := hirr
  have hfixV : fixV ρ D = ⊥ := by
    rw [← hfix]
    exact Submodule.ext fun v => Iff.rfl
  have hH : CFSG.pPrimeCore 3 G ≤ Subgroup.center G := pPrimeCore_three_le_center hSz hK ρ hρ hD hgen hfixV
  have hodd : Odd (Nat.card (Subgroup.center G)) := odd_card_center_of_irreducible_two ρ hρ
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center G) := UC46.not_three_dvd_card_center h3 hD hgen hperf
  have hsimple : IsSimpleGroup (G ⧸ Subgroup.center G) :=
    UC46.isSimpleGroup_quotient_center h3 hD hgen hperf hH
  have hnab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    apply UC46.center_ne_top hD hperf
    have hle : commutator G ≤ Subgroup.center G := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 fun x _ y _ => ?_
      rw [← QuotientGroup.eq_one_iff]
      simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm (x : G ⧸ Subgroup.center G) (y : G ⧸ Subgroup.center G)]
      group
    rw [hperf] at hle
    exact eq_top_iff.2 hle
  have hqs : CFSG.IsQuasisimple G := ⟨Group.isPerfect_def.2 hperf, hsimple, hnab⟩
  have hKq : CFSG.Open.IsKGroup (G ⧸ Subgroup.center G) := hK.quotient _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ Subgroup.center G)) = 1 := by
    rw [CFSG.SectionRank.pRank_quotient_eq _ h3Z]
    exact h3
  have hL := hK32 (G ⧸ Subgroup.center G) hKq hsimple hnab hrank
  have hZ : Subgroup.center G = ⊥ := center_eq_bot_of_catalog hGA hSp hqs hodd h3Z hL
  rcases hL with ⟨p, f, hm⟩ | ⟨p, f, hq, hm⟩ | ⟨p, f, hq, hm⟩ | hJ
  · exact Or.inl ⟨p, f, LieModel.of_quotient_center hZ hm⟩
  · exact Or.inr (Or.inl ⟨p, f, hq, LieModel.of_quotient_center hZ hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨p, f, hq, LieModel.of_quotient_center hZ hm⟩))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    obtain ⟨e⟩ := hJ
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

section


theorem k46List_holds
    : K46List :=
  k46List_of_inputs kSz_holds k32_holds CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
    CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds

end

end CFSG.LocalAnalysis.UniquenessCase.UCK
