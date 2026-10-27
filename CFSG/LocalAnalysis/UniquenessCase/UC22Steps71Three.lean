module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps70Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2C
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeN
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps71Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s21_8U : S21_8U D Ch
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

section Certified


set_option linter.unusedSectionVars false

theorem Steps71Three.toSteps70Three {D : Data G} {Ch : Choice2011 G} (h : Steps71Three D Ch)
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h211 : S21_1 D Ch)
    (h15 : S21_15C D Ch) (h8100 : R8100U2 D) : Steps70Three D Ch where
  s21_14 := h.s21_14
  s21_8 := s21_8Sp4_of_s21_8U hSg h211 h.s21_8U
  s22_5_1R3 := h.s22_5_1R3
  s21_12R3 := h.s21_12R3
  r8_2 := h.r8_2
  s21_3 := h.s21_3
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3 := s21_22R3_of_residuals hSg h13 h211
    (F08.R869NS5_of_R869NS _ (F08.R869NS_of_R869N _ h.r8_69N))
    (F08.R869NPair_of_R869N _ h.r8_69N) h15 h8100 h.s21_22R3F3
    h.s21_22R3E5 h.s21_22R3NoPair
  s22_fin3R := s22Fin3R_of_s20_14N h.s20_14N h.s22FinA

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
