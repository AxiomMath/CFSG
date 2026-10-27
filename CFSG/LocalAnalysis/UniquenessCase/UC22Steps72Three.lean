module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps71Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Steps72Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1R3 : S22_5_1R3 D Ch
  s21_12R3 : S21_12R3 D Ch
  r8_2 : F08.R82 D
  s21_3 : S21_3 D Ch
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3 : S21_22R3F3 D Ch
  s21_22R3E5 : S21_22R3E5 D Ch
  s21_22R3NoPair : S21_22R3NoPair D Ch
  r8_100U2D : R8100U2D D
  s20_14N : S20_14N D
  s22FinA : S22FinA D Ch

theorem Steps72Three.toSteps71Three {D : Data G} {Ch : Choice2011 G} (h : Steps72Three D Ch)
    (h8U : S21_8U D Ch) : Steps71Three D Ch where
  s21_14 := h.s21_14
  s21_8U := h8U
  s22_5_1R3 := h.s22_5_1R3
  s21_12R3 := h.s21_12R3
  r8_2 := h.r8_2
  s21_3 := h.s21_3
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3F3 := h.s21_22R3F3
  s21_22R3E5 := h.s21_22R3E5
  s21_22R3NoPair := h.s21_22R3NoPair
  r8_100U2D := h.r8_100U2D
  s20_14N := h.s20_14N
  s22FinA := h.s22FinA

end CFSG.LocalAnalysis.UniquenessCase.UC22
