module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.R8101RankFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

variable {G : Type} [Group G] [Finite G]

theorem gap17_45_uniqueMaxFive_of_SE
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S)) (V₀ V : Subgroup G)
    (hg5 : S17.Gap17_45_UniqueMaxFiveSE (UC6.dataOfSetup4 hS hU S) V₀ V) :
    S17.Gap17_45_UniqueMaxFive (UC6.dataOfSetup4 hS hU S) V₀ V := by
  intro L X p n l r C Dc Gamma x A₀ A B hV₀ hctx h8100 hcase hSyl hTA hBM hcard hcomm hTB
    hcent
  have hσ : p ∈ (UC6.dataOfSetup4 hS hU S).sig := h8100.2.2.2.2.2.1
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p
      (UC6.dataOfSetup4 hS hU S).M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sigmaStd_dataOfSetup4 hS hU S)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC (h8100.1 0)) hσ
  exact hg5 L X p n l r C Dc Gamma x A₀ A B hV₀ hctx h8100 hcase hSyl hTA hBM hcard hcomm
    hTB hcent hsp (r8101_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847)

theorem gap17_45_uniqueMaxFive_setup4_of_nonabChief
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G)
    (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h847 : F08.R847 (UC6.dataOfSetup4 hS hU S)) (V₀ V : Subgroup G)
    (hN : S17.Gap17_45_NonabChief (UC6.dataOfSetup4 hS hU S) V₀ V) :
    S17.Gap17_45_UniqueMaxFive (UC6.dataOfSetup4 hS hU S) V₀ V :=
  gap17_45_uniqueMaxFive_of_SE hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 V₀ V
    (gap17_45_uniqueMaxFiveSE_of_nonabChief (UC6.dataOfSetup4 hS hU S) V₀ V hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
