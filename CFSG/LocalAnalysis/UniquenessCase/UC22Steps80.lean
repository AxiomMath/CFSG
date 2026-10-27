module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps79
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest7
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

structure Steps80 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest : S21_3Rest7 D Ch
  s21_14R : S21_14R D Ch
  s21_8XE : S21_8XE D Ch
  s21_12aR2 : S21_12aFR2 D (Choice214U D)
  s21_12aR34 : S21_12aFR34 D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

theorem Steps80.toSteps79 (hSE : StronglyEmbeddedFive) (hOut : RankThreeTheoremC.KFactOutCyclic)
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hSC : PartTwo.Inputs1719.K_SporadicCoverCenterOdd)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hE : UC22P20gExcFacts)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (Ch : Choice2011 G)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → Ch L₀ B₀)
    (h207 : S20_7 (UC6.dataOfSetup4 hS hU S)) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (h : Steps80 (UC6.dataOfSetup4 hS hU S) Ch) :
    Steps79 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest := s21_3Rest5_of_rest6 hS hU S hMS hSE hOut hrank hout hSC Ch
    (s21_3Rest6_of_rest7 hGA h.s21_3Rest)
  s21_14R := h.s21_14R
  s21_8XE := h.s21_8XE
  s21_12a := s21_12aFU_of_residual hE h207 h5 hCh h.s21_12aR2 h.s21_12aR34

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
