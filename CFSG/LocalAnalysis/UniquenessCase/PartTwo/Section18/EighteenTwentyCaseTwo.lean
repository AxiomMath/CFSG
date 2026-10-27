module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTwoAset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem eighteen_twenty_of_K2 (hK : K_Omega6Minus_sumOfTwo_aParam) (D : Data G)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hSg : UC6S846.SigmaStd D) (h142 : R18_14_2At D V₀ V p L h)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h1742 : S17.R17_42 D) :
    R18_20At D V₀ V p L h := by
  intro s hs
  obtain ⟨-, -, f, hO, -⟩ := id hs
  obtain ⟨-, hf1, -⟩ := r18_fieldOmega D h1742 V₀ V p L h f hO
  have h15 : R18_15At D V₀ V p L := r18_15_of_case2 D h h142 hs (by omega) hO
  exact eighteen_twenty_of_K hK D V₀ V p L h hx h61 h126 h66 h127 h1114 h111 h183 h1669 h16 h17
    (eighteen_eighteen_b D hSg h h15) h1742 s hs

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
