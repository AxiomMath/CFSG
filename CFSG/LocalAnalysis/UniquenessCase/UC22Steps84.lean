module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps83
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Glue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

structure Steps84 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest8 : S21_3Rest8 D Ch
  s21_14R4 : S21_14R4 D Ch
  s21_14R3U : S21_14R3U D Ch
  s21_14R3L : S21_14R3L D Ch
  s21_14D4 : S21_14D4 D Ch
  s21_14K2 : S21_14K2 D Ch
  s21_14L34 : S21_14L34 D Ch
  s21_12aR34L3 : S21_12aFR34L3 D (Choice214U D)
  s21_12aR34F2 : S21_12aFR34F2 D (Choice214U D)
  s21_12aR34F3 : S21_12aFR34F3 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedSectionVars false


theorem Steps84.toSteps83 (hGA : CFSG.Open.GriessAllModelsStatement) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S))
    (hn3 : H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch, 3 ≤ c.n)
    (h3 : S21_3 (UC6.dataOfSetup4 hS hU S) Ch) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S)) (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → Ch L₀ B₀)
    (h : Steps84 (UC6.dataOfSetup4 hS hU S) Ch) : Steps83 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest8 := h.s21_3Rest8
  s21_14R := s21_14R_setup4_of_residuals hGA hS hU S hPart Ch h76 hn3 h3 h5 h.s21_14R4 h.s21_14R3U
    h.s21_14R3L h.s21_14D4 h.s21_14K2 h.s21_14L34
  s21_12aR34 := s21_12aFR34_of_rest hGA h82 h211 hCh h.s21_12aR34L3 h.s21_12aR34F2 h.s21_12aR34F3

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
