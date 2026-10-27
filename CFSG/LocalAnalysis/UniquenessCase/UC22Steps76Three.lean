module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps75Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3ND
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps76Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1RStar : S22_5_1RStar D Ch
  s21_12aR34L3P : S21_12aFR34L3P D (Choice214U D)
  s21_12aR34F2 : S21_12aFR34F2 D (Choice214U D)
  r8_2 : F08.R82 D
  r8_69NRest3 : F08.R869NRest3 D
  r8_69MConsRest3 : F08.R869MConsRest3 D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3SzQ5T : S21_22R3F3SzQ5T D Ch
  s21_22R3E5R : S21_22R3E5R D Ch
  s21_22R3NoPairR : S21_22R3NoPairR D Ch

section Certified


theorem Steps76Three.toSteps75Three {D : Data G} {Ch : Choice2011 G} (h : Steps76Three D Ch)
    (hGA : CFSG.Open.GriessAllModelsStatement) (h211 : S21_1 D Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U D L₀ B₀ → Ch L₀ B₀)
    (hL3 : S21_12aFR34L3 D (Choice214U D)) (hF3 : S21_12aFR34F3 D (Choice214U D))
    (h3NN4 : S21_3RestNN4 D Ch) (hs : Standing22 D) (hCen : UCK.U3Center)
    (h846 : F08.R846 D) (h219 : S21_9Sig3 D Ch) (h17 : S21_17 D Ch) (h21U3 : S21_21U3 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) :
    Steps75Three D Ch where
  s21_14 := h.s21_14
  s22_5_1RStar := h.s22_5_1RStar
  s21_12aR34 := s21_12aFR34_of_rest hGA h.r8_2 h211 hCh hL3 h.s21_12aR34F2 hF3
  r8_2 := h.r8_2
  s21_3NN4 := h3NN4
  r8_69NRest3 := h.r8_69NRest3
  r8_69MConsRest3 := h.r8_69MConsRest3
  r8_80J4 := h.r8_80J4
  s21_22R3F3SzQ5T := h.s21_22R3F3SzQ5T
  s21_22R3E5R := h.s21_22R3E5R
  s21_22R3NoPair := s21_22R3NoPair_of_s21_22R3NoPairR hs hCen h211 h846 h219 h17 h21U3 hn3
    h.s21_22R3NoPairR

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
