module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenNineteenCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneCaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaFourPlusNormalizerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTwoAsetHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaFourPlusSmallCommHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOneTwoHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixteen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem eighteen_twentytwo_of_K (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G)
    (h : Hyp18 D V₀ V p L) (h13 : R18_13At D V₀ V p L h)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (hSg : UC6S846.SigmaStd D)
    (h1742 : S17.R17_42 D) (h4 : R18_4At D V₀ V p L)
    (h142 : R18_14_2At D V₀ V p L h) (h172 : R18_17_2At D V₀ V p L h) :
    R18_22At D V₀ V p L h := by
  have hKi2 : K_18_21_i2 := k_K_18_21_i2_holds
  have hKts : K_SU4Nat_totallySingular := k_K_SU4Nat_totallySingular_holds
  have h42 : S17.R17_42At D V₀ V := h1742 V₀ V h.hyp125
  have h141 : R18_14_1At D V₀ V p L h :=
    eighteen_fourteen_one D V₀ V p L h h42
  have h143 : R18_14_3At D V₀ V p L h :=
    eighteen_fourteen_three D V₀ V p L h h42
  have h161 : R18_16_1At D V₀ V p L h := eighteen_sixteen_one D h61 V₀ V p L h h42 h141 hKts
  have h162 : R18_16_2At D V₀ V p L h := eighteen_sixteen_two D h61 V₀ V p L h h42 h142
  have h171 : R18_17_1At D V₀ V p L h := eighteen_seventeen_one_of_K D V₀ V p L h h61 h42
  have hKns3 : K_Omega4Plus_nonsingPoint := k_K_Omega4Plus_nonsingPoint_holds
  have hKsc3 : K_Omega4Plus_smallComm := k_K_Omega4Plus_smallComm_holds
  exact eighteen_twentytwo D V₀ V p L h h13
    (eighteen_nineteen_of_K3 hKns3 hKsc3 k_OmegaFourPlusNormalizer_pRank_holds D V₀ V p L h
      hx h61 h126 h66 h127 h1114 h111 h183 h1669 hSg h143 (h1742 V₀ V h.hyp125) h4)
    (eighteen_twenty_of_K2 k_Omega6Minus_sumOfTwo_aParam_holds D V₀ V p L h hx h61 h126 h66 h127
      h1114 h111 h183 h1669 hSg h142 h162 h172 h1742)
    (eighteen_twentyone_of_case1 D h hx h61 h126 h66 h127 h1114 h111 h183 h1669
      (h1742 V₀ V h.hyp125) h141 hSg h161 h171 hKi2)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
