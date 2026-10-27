module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem eighteen_twentyone_of_case1 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h1742 : S17.R17_42At D V₀ V)
    (h141 : R18_14_1At D V₀ V p L h)
    (hSg : UC6S846.SigmaStd D)
    (h16 : R18_16_1At D V₀ V p L h) (h17 : R18_17_1At D V₀ V p L h)
    (hKi2 : K_18_21_i2) :
    R18_21At D V₀ V p L h := fun hP =>
  have h15 : R18_15At D V₀ V p L := r18_15_of_case1 D h h1742 h141 hP
  eighteen_twentyone D h hx h61 h126 h66 h127 h1114 h111 h183 h1669 h1742 h141 h15 hSg
    h16 h17 (eighteen_eighteen_b D hSg h h15) hKi2 hP

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
