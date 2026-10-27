module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps82
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)

structure Steps83 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest8 : S21_3Rest8 D Ch
  s21_14R : S21_14R D Ch
  s21_12aR34 : S21_12aFR34 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedSectionVars false


theorem Steps83.toSteps82 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree)
    (hOut : RankThreeTheoremC.KFactOutCyclic) (hGA : CFSG.Open.GriessAllModelsStatement)
    (h33 : UCK.K33) (h31 : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (Ch : Choice2011 G) (h : Steps83 (UC6.dataOfSetup4 hS hU S) Ch) :
    Steps82 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest := s21_3Rest7_of_rest8 hS hU S hMS hPart hSE hSS hK3 hB3 hOut hGA h33 h31 Ch
    h.s21_3Rest8
  s21_14R := h.s21_14R
  s21_12aR34 := h.s21_12aR34

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
