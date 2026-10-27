module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R871
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKOmegaCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R875O2HM
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R876
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R877
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R878
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R879

import CFSG.CGT.PushingUpLit.CGT6.EmbEndSporThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R876K762
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKOutPComplement
import CFSG.LocalAnalysis.UniquenessCase.UC1K32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem r869_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G)
    (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D) (h614 : UC6.R6_14 D) (h638 : UC6.R6_38 D)
    (h76 : UC22.F07.R76 D) (hSg : UC6S846.SigmaStd D) (h870 : R870 D)
    (h82 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R82 D) (h856 : R856 D) (h872 : R872 D)
    (h67 : UC6.R6_7 D) (hK328 : K328) (hK329 : K329) (hK335 : K335)
    (hY : Eight73YLieModel D) (hS7 : S7_876 D) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R869 D := by
  have hK32 : UCK.K32 := UCK.k32_holds
  have hK762 : K762 := k762_holds
  have hGA : GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes :=
    CFSG.CGT.PushingUpLit.CGT6.sporadicThreeCenterSmallPrimes_holds
  have hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group) := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have hOut : OutPComplement := fun _ _ _ hq hcat _ hp hp2 h1 =>
    hasNormalPComplement_outer_of_quasisimple_of_pRank_le_one hq hcat hp hp2 h1
  have hKSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch :=
    CFSG.LocalAnalysis.RankThreeUC.S15.kSch_of_catalog CFSG.AGLEmbedding.kFactCatalogSchreier
  have h871 : R871 D :=
    r871_of_inputs D hGA hSpor hM22 h63 h69 h614 h638 h76 hSg h870 hOut h82 h856
  have hOmega : OmegaCentral :=
    ⟨fun hX hr h5 hd R hR hs => omega_inner_central_psl_three_two_pow hX hr h5 hd R hR hs,
      fun hX hr h5 hd R hR hs => omega_inner_central_psu_three_two_pow hX hr h5 hd R hR hs⟩
  have h873Mod : R873Mod D :=
    r873Mod_of_inputs hGA hSp hK32 hSg h870 h871 h872 h614 h76 h638 hOut hOmega hY
  have h874 : R874 D := r874_of_m3 D h63 h871 (r873M3_of_r873Mod h873Mod)
  have hO2 : R875O2HM D := r875O2HM_of_inputs D hSg h873Mod h874 h67
  have h873 : R873 D := r873_of_r873Mod h873Mod hO2
  have h875c : R875Comp D := r875Comp_of_inputs D h873 hO2
  have h873M3 : R873M3 D := r873M3_of_r873 h873
  have hQN : R875QNorm D := r875QNorm_of_inputs D hGA hSg h870 h873 h875c
  have h875 : R875 D :=
    r875_of_parts (r875Ex_of_inputs D h873M3 h874 h875c)
      (r875Le_of_inputs D hKSch hSg h870 h873 h874 h875c hQN)
      (r875NotLe_of_inputs D h63 h873M3 h874 h875c)
  have h876 : R876 D := r876_of_inputs D h63 hSg h870 h873 h874 hQN hK762 hS7
  have h877 : R877 D := r877_of_inputs D hK328 hGA hSg h870 h873 h874 h875 h875c
  have h878 : R878 D := r878_of_inputs D hK335 hGA hSg h870 h873 h874 h875 h875c h876 h877
  have h879 : R879 D := r879_of_inputs D hK329 hSg h870 h874 h875 h875c
  exact r869_of_spine D h878 h879

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
