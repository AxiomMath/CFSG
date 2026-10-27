module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps85
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest14
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Head

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)

structure Steps86 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest14 : S21_3Rest14 D Ch
  s21_14R4 : S21_14R4 D Ch
  s21_14R3U : S21_14R3U D Ch
  s21_14R3L : S21_14R3L D Ch
  s21_12aR34L3 : S21_12aFR34L3 D (Choice214U D)
  s21_12aR34F2 : S21_12aFR34F2 D (Choice214U D)
  s21_12aR34F3 : S21_12aFR34F3 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]


theorem Steps86.toSteps85 (hgr : CFSG.Open.GriessAllModelsStatement) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (Ch : Choice2011 G) (h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S))
    (h : Steps86 (UC6.dataOfSetup4 hS hU S) Ch) : Steps85 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest10 := s21_3Rest10_of_rest11 hgr hS hU S hMS hPart hSE hSS hK3 hB hOut Ch
    (s21_3Rest11_of_rest12 hgr hS hU S hMS hPart hSE hSS hK3 hB hOut Ch
      (s21_3Rest12_of_rest13 hgr hS hU S hMS hPart hSE hSS hK3 hB hOut Ch
        (s21_3Rest13_of_rest14 hgr hS hU S hMS hPart hSE hOut Ch h.s21_3Rest14)))
  s21_14R4 := h.s21_14R4
  s21_14R3U := h.s21_14R3U
  s21_14R3L := h.s21_14R3L
  s21_14D4 := s21_14D4_setup4 hS hU S hPart Ch h76
  s21_14K2 := s21_14K2_setup4 hgr hS hU S hPart Ch h76
  s21_12aR34L3 := h.s21_12aR34L3
  s21_12aR34F2 := h.s21_12aR34F2
  s21_12aR34F3 := h.s21_12aR34F3

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
