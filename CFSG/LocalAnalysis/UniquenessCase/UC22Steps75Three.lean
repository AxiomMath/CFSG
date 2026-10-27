module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps74Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3KC
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251q

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps75Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1RStar : S22_5_1RStar D Ch
  s21_12aR34 : S21_12aFR34 D (Choice214U D)
  r8_2 : F08.R82 D
  s21_3NN4 : S21_3RestNN4 D Ch
  r8_69NRest3 : F08.R869NRest3 D
  r8_69MConsRest3 : F08.R869MConsRest3 D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3SzQ5T : S21_22R3F3SzQ5T D Ch
  s21_22R3E5R : S21_22R3E5R D Ch
  s21_22R3NoPair : S21_22R3NoPair D Ch

section Certified


theorem Steps75Three.toSteps74Three {D : Data G} {Ch : Choice2011 G} (h : Steps75Three D Ch)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h119 : R119W D) (h17 : S21_17 D Ch) (h211 : S21_1 D Ch)
    (h2112 : S21_12 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hSg : UC6S846.SigmaStd D) (h847 : R847E3L3 D)
    (h920 : PartOne.Section9.R920odd D) (h923 : F09.R923 D) (h8107 : F08.R8107 D)
    (h3NN : S21_3RestNN D Ch) (h15 : S21_15C D Ch) (hNN : R847E3ThinNNOut D) :
    Steps74Three D Ch where
  s21_14 := h.s21_14
  s22_5_1R3K2 := s22_5_1R3K2_of_rStar D Ch hx h61 h119 h17 h211 h2112 h31 h33 hn3 hSg h847 h920
    h923 h8107 h.s22_5_1RStar
  s21_12aR34 := h.s21_12aR34
  r8_2 := h.r8_2
  s21_3NN := h3NN
  r8_69NRest3 := h.r8_69NRest3
  r8_69MConsRest3 := h.r8_69MConsRest3
  r8_80J4 := h.r8_80J4
  s21_22R3F3SzQ := s21_22R3F3SzQ_of_s21_22R3F3SzQ5 hSg h15 hNN
    (s21_22R3F3SzQ5_of_s21_22R3F3SzQ5T hSg h15 hNN h.s21_22R3F3SzQ5T)
  s21_22R3E5R := h.s21_22R3E5R
  s21_22R3NoPair := h.s21_22R3NoPair

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
