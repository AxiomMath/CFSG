module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps73Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5R
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251o
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R869NThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R869MConsThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HD
import CFSG.LocalAnalysis.UniquenessCase.UC22FinAMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps74Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1R3K2 : S22_5_1R3K2 D Ch
  s21_12aR34 : S21_12aFR34 D (Choice214U D)
  r8_2 : F08.R82 D
  s21_3NN : S21_3RestNN D Ch
  r8_69NRest3 : F08.R869NRest3 D
  r8_69MConsRest3 : F08.R869MConsRest3 D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3SzQ : S21_22R3F3SzQ D Ch
  s21_22R3E5R : S21_22R3E5R D Ch
  s21_22R3NoPair : S21_22R3NoPair D Ch

section Certified


theorem Steps74Three.toSteps73Three {D : Data G} {Ch : Choice2011 G} (h : Steps74Three D Ch)
    (h1 : S22_5_1K1 D Ch) (h12 : S21_12R3 D Ch) (h3 : S21_3 D Ch) (h869N : F08.R869N D)
    (h869M : F08.R869MCons D) (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D)
    (h211 : S21_1 D Ch) (h8107 : F08.R8107 D) (h15 : S21_15C D Ch) (h847T : R847E3Thin D)
    (h16 : S21_16 D Ch) (h17 : S21_17 D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (h8100 : R8100U2 D) (h2014 : S20_14N D) (hB : ListBNonabelian) (h205 : S20_5 D) :
    Steps73Three D Ch where
  s21_14 := h.s21_14
  s22_5_1R3 := s22_5_1R3_of_s22_5_1R3K2 h1 h.s22_5_1R3K2
  s21_12R3 := h12
  r8_2 := h.r8_2
  s21_3 := h3
  r8_69N := h869N
  r8_69M := h869M
  r8_80J4 := h.r8_80J4
  s21_22R3F3SzQ := h.s21_22R3F3SzQ
  s21_22R3E5 := s21_22R3E5_of_s21_22R3E5R hSg h13 h211 h.r8_2 h8107
    (F08.R869NS5_of_R869NS _ (F08.R869NS_of_R869N _ h869N)) h15 h847T h16 h17 hn3
    h.s21_22R3E5R
  s21_22R3NoPair := h.s21_22R3NoPair
  r8_100U2D := r8100U2D_of_r8100U2 h8100
  s20_14N := h2014
  s22FinA := FinA.s22FinA_of_inputs D Ch hB h205 hSg

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
