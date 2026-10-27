module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps67Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112E3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps70Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s21_8 : S21_8Sp4 D Ch
  s22_5_1R3 : S22_5_1R3 D Ch
  s21_12R3 : S21_12R3 D Ch
  r8_2 : F08.R82 D
  s21_3 : S21_3 D Ch
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3 : S21_22R3 D Ch
  s22_fin3R : S22Fin3R D Ch

theorem Steps70Three.toSteps67Three {D : Data G} {Ch : Choice2011 G} (h : Steps70Three D Ch)
    (h12 : S21_12 D Ch) (h17 : S21_17RJ1 D Ch) (h2121 : S21_21TB D Ch)
    (h219 : S21_9Sig3 D Ch) : Steps67Three D Ch where
  s21_14 := h.s21_14
  s21_8 := h.s21_8
  s21_21TB := h2121
  s22_5_1R3 := h.s22_5_1R3
  s21_12 := h12
  s21_17RJ1 := h17
  r8_2 := h.r8_2
  s21_3 := h.s21_3
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3 := h.s21_22R3
  s21_9Sig3 := h219
  s22_fin3R := h.s22_fin3R

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
