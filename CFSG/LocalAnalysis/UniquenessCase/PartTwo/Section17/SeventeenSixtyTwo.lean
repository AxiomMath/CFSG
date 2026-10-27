module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34FixHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyTwoFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem seventeen_sixtytwo (D : Data G) {V₀ V : Subgroup G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h614 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_14 D)
    (h61 : R17_61At D V₀ V)
    (h59 : R17_59At D V₀ V)
    (h869 : F08.R869 D)
    (h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3 D)
    (h69 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_9 D)
    (hThin : CFSG.LocalAnalysis.UniquenessCase.PartTwo.ThinList13) :
    R17_62At D V₀ V := by
  intro L p ctx
  by_contra hk1
  have hk2 : D.k = 2 := by
    have := TwelveShort.one_le_k D
    have := TwelveSeven.k_le_two D
    omega
  obtain ⟨E, P, hEP, hEcent, hEea, hEcard, hPsyl, hΓ⟩ :=
    exists_elemAbelian_three_central_sylow D ctx hSg hThin hk2 h61 h59 h869 h63 h69
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_L34Fix_holds
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  have hsigsub : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_cases h3 : 3 ∈ D.sig
    · exact hSg.sig1_sp 3 (hsigsub h3)
    · refine h614 hsigsub 3 Nat.prime_three (by norm_num) h3 P hPsyl E ?_ hEea hEcard hΓ
      exact le_inf hEP hEcent
  exact ((Data.k_eq_two_iff D).mp hk2) hsp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
