module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps80
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

structure Steps81 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest : S21_3Rest7 D Ch
  s21_14R : S21_14R D Ch
  s21_8XE2 : S21_8XE2 D Ch
  s21_12aR2g : S21_12aFR2g D (Choice214U D)
  s21_12aR2d : S21_12aFR2d D (Choice214U D)
  s21_12aR34 : S21_12aFR34 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]


theorem Steps81.toSteps80 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hσ : UC6S846.SigmaStd (UC6.dataOfSetup4 hS hU S)) (hKF7 : KF7Use (UC6.dataOfSetup4 hS hU S))
    (h : Steps81 (UC6.dataOfSetup4 hS hU S) Ch) :
    Steps80 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest := h.s21_3Rest
  s21_14R := h.s21_14R
  s21_8XE := s21_8XE_of_s21_8XE2_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211 h.s21_8XE2
  s21_12aR2 := s21_12aFR2_of_rest hGA hσ hKF7 h.s21_12aR2g h.s21_12aR2d
  s21_12aR34 := h.s21_12aR34

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
