module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps84
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest10
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L34

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable BadNoStrongThree)

structure Steps85 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest10 : S21_3Rest10 D Ch
  s21_14R4 : S21_14R4 D Ch
  s21_14R3U : S21_14R3U D Ch
  s21_14R3L : S21_14R3L D Ch
  s21_14D4 : S21_14D4 D Ch
  s21_14K2 : S21_14K2 D Ch
  s21_12aR34L3 : S21_12aFR34L3 D (Choice214U D)
  s21_12aR34F2 : S21_12aFR34F2 D (Choice214U D)
  s21_12aR34F3 : S21_12aFR34F3 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

theorem Steps85.toSteps84 (hgr : CFSG.Open.GriessAllModelsStatement) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable) (hB : BadNoStrongThree)
    (h846 : F08.R846 (UC6.dataOfSetup4 hS hU S)) (Ch : Choice2011 G)
    (h : Steps85 (UC6.dataOfSetup4 hS hU S) Ch) : Steps84 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest8 := s21_3Rest8_of_rest9 (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    (s21_3Rest9_of_rest10 hgr hS hU S hMS hPart hSE hSS hB h846 Ch h.s21_3Rest10)
  s21_14R4 := h.s21_14R4
  s21_14R3U := h.s21_14R3U
  s21_14R3L := h.s21_14R3L
  s21_14D4 := h.s21_14D4
  s21_14K2 := h.s21_14K2
  s21_14L34 := s21_14L34_holds _ Ch
  s21_12aR34L3 := h.s21_12aR34L3
  s21_12aR34F2 := h.s21_12aR34F2
  s21_12aR34F3 := h.s21_12aR34F3

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
