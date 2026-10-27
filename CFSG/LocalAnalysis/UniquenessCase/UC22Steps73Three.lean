module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps72Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3S

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps73Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1R3 : S22_5_1R3 D Ch
  s21_12R3 : S21_12R3 D Ch
  r8_2 : F08.R82 D
  s21_3 : S21_3 D Ch
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3SzQ : S21_22R3F3SzQ D Ch
  s21_22R3E5 : S21_22R3E5 D Ch
  s21_22R3NoPair : S21_22R3NoPair D Ch
  r8_100U2D : R8100U2D D
  s20_14N : S20_14N D
  s22FinA : S22FinA D Ch

section Certified


theorem Steps73Three.toSteps72Three {D : Data G} {Ch : Choice2011 G} (h : Steps73Three D Ch)
    (h8107 : F08.R8107 D) (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (h8100 : R8100U2 D) :
    Steps72Three D Ch where
  s21_14 := h.s21_14
  s22_5_1R3 := h.s22_5_1R3
  s21_12R3 := h.s21_12R3
  r8_2 := h.r8_2
  s21_3 := h.s21_3
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3F3 := s21_22R3F3_of h8107 hSg h15 h8100 h.s21_22R3F3SzQ
  s21_22R3E5 := h.s21_22R3E5
  s21_22R3NoPair := h.s21_22R3NoPair
  r8_100U2D := h.r8_100U2D
  s20_14N := h.s20_14N
  s22FinA := h.s22FinA

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
