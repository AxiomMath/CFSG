module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteenCaseThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaPlusFourAsetHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem eighteen_nineteen_of_K3
    (hKns : K_Omega4Plus_nonsingPoint) (hKsc : K_Omega4Plus_smallComm)
    (hKp : K_OmegaFourPlusNormalizer_pRank)
    (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (hSg : UC6S846.SigmaStd D)
    (h143 : R18_14_3At D V₀ V p L h) (h1742 : S17.R17_42At D V₀ V)
    (h4 : R18_4At D V₀ V p L) :
    R18_19At D V₀ V p L h := fun h3 =>
  have h638 : UC6.R6_38 D := r6_38_of_hyp18 D h hSg
  eighteen_nineteen_of_K k_Omega4Plus_aParam_le_holds D V₀ V p L h hx h61 h126 h66 h127
    h1114 h111 h183 h1669
    (eighteen_sixteen_three_weak D h61 V₀ V p L h h1742 h143 hKns hSg hKp h638)
    (eighteen_seventeen_three_of_K D V₀ V p L h h61 hSg hKsc hKp h638 h1742)
    (eighteen_eighteen_b D hSg h (r18_15_of_case3 D h h1742 hSg hKp h3)) h1742 h4 h3

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
