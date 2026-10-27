module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps81
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5X
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Gamma
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2d
import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardFour
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

structure Steps82 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest : S21_3Rest7 D Ch
  s21_14R : S21_14R D Ch
  s21_12aR34 : S21_12aFR34 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

theorem Steps82.toSteps81
    (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) (Ch : Choice2011 G) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (h : Steps82 (UC6.dataOfSetup4 hS hU S) Ch) :
    Steps81 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest := h.s21_3Rest
  s21_14R := h.s21_14R
  s21_8XE2 := s21_8XE2_of_s21_8XE3_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211
    (s21_8XE3_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211)
  s21_12aR2g := s21_12aFR2g_of_r74Card hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (F07.r74Card_dataOfSetup4 hSE hK3 hB3 hS hU S hMS hPart.1)
  s21_12aR2d := s21_12aFR2d_dataOfSetup4 hGA hSE hK3 hB3 hS hU S hMS hPart
  s21_12aR34 := h.s21_12aR34

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
