module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps78
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20zk
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest5
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

structure Steps79 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest : S21_3Rest5 D Ch
  s21_14R : S21_14R D Ch
  s21_8XE : S21_8XE D Ch
  s21_12a : S21_12aF D (Choice214U D)

section Setup

variable {G : Type} [Group G] [Finite G]

theorem Steps79.toSteps78 (hSE : StronglyEmbeddedFive) (hK3 : StronglyEmbeddedThree)
    (hB3 : BadNoStrongThree) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hOut : RankThreeTheoremC.KFactOutCyclic)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hE : UC22P20gExcFacts) (hu38 : uc22p20oU38Witness) (hB : ListBNonabelian)
    (hO : LieOrderFormulasInput) (hThin : PartTwo.ThinList13) (hK : PartTwo.S17.K_LieModelNotL2)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) (Ch : Choice2011 G)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → Ch L₀ B₀)
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch) (h207 : S20_7 (UC6.dataOfSetup4 hS hU S))
    (h3 : S21_3 (UC6.dataOfSetup4 hS hU S) Ch) (h : Steps79 (UC6.dataOfSetup4 hS hU S) Ch) :
    Steps78 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest := s21_3Rest4_of_rest5 hS hU S hMS hSE hOut hout Ch h.s21_3Rest
  s21_14 := s21_14_of_s21_14R_setup4 hSE hK3 hB3 hGA hS hU S hMS hPart Ch h211 h.s21_8XE h.s21_14R
  s21_12a := s21_12aF_of_choice214U hE hu38 hB hO hThin hK h207 h3 hCh h.s21_12a

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
