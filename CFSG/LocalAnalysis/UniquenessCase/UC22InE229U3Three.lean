module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R847E4
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3Orb
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229U3E9
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCKPSyl1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem r847U3Three_of_conclusion76 (D : Data G) (hSg : UC6S846.SigmaStd D) (hCen : UCK.U3Center)
    (hSyl : UCK.U3SylOmega) (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h76 : D.k = 2 → ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) :
    R847U3Three D := by
  intro Y hY X hXY hXc n hX h3
  have hYM : Y ≤ D.M := hY.1.le
  have hXel : IsElemAbelian 3 X := UC6S898.isElemAbelian_of_card_prime Nat.prime_three hXc
  by_cases hs3 : IsStronglyPEmbedded 3 D.M
  · have hX1 : X ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hXc
      omega
    exact hs3.normalizer_le hX1 hXel.isPGroup (hXY.trans hYM)
  have hns := UC6S846.not_solvable_of_mem_calC hY
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hs3 hsp
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  have h3r : CFSG.Open.pRank 3 D.M ≤ 3 := by
    by_contra h
    exact hs3 (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem 3 Nat.prime_three (by norm_num)
      (by omega)))
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp hsp
  obtain ⟨E, X', hXE, hEY, hEel, hEc, hX'E, hX'c, hX'Z⟩ :=
    uc22ine229u3e9_exists_E hX h3 (hCen (Bar2 Y) n hX) hXY hXc
  have hEM : E ≤ D.M := hEY.trans hYM
  have h2 := uc22ine229u3orb_two_le_pRank hSyl hY hX hp hp5 hOp (h4 p hpσ) hEY Nat.prime_three
    (by norm_num) hEel.isPGroup (hX'E.trans hEY) hX'c
    (fun x hx hc => congrArg Subtype.val (hX'Z x hx hc)) h3r
  have h76p := h76 ((Data.k_eq_two_iff D).2 hs3) p hpσ hsp
  have hΓ : rankThreeGamma 1 3 E ≤ D.M := by
    refine h76p 3 Nat.prime_three E hEM hEel hEc (by omega) fun Z hZE _ => ?_
    refine lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_))
    exact inf_le_inf_left _ ((Subgroup.centralizer_le hZE).trans
      (Subgroup.centralizer_le_normalizer _))
  have hrank : 1 ≤ CFSG.Open.pRank 3 X :=
    UC6S846.le_pRank' Nat.prime_three le_rfl hXel (by rw [hXc, pow_one])
  exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hXE hrank).trans hΓ

theorem r847U3Three_setup4 (hSE : StronglyEmbeddedFive) (hgr : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) :
    R847U3Three (UC6.dataOfSetup4 hS hU S) :=
  r847U3Three_of_conclusion76 _ (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (UCK.u3Center_of_griess hgr) (UCK.u3SylOmega_of_griess hgr)
    (fun _ hp => UC6.four_le_pRank_of_sigma hp)
    (fun hk _ hp hsp => conclusion76_setup4_k_eq_two hSE hS hU S hσ hk hp hsp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
