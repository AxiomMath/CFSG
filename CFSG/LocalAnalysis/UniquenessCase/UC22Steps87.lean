module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps86
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213CharY
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U7KFacts
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UHead
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunCommute
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20r

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)

structure Steps87 {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) : Prop where
  s21_3Rest15 : S21_3Rest15 D Ch
  s21_14R4F : S21_14R4F D Ch
  s21_14R3UF : S21_14R3UF D Ch
  s21_14R3L : S21_14R3L D Ch
  s21_12aR34L3P : S21_12aFR34L3P D (Choice214U D)
  s21_12aR34L3E : S21_12aFR34L3E D (Choice214U D)
  s21_12aR34F2Q35 : S21_12aFR34F2Q35 D (Choice214U D)
  s21_12aR34F2Sig : S21_12aFR34F2Sig D (Choice214U D)
  s21_12aR34F2Even : S21_12aFR34F2Even D (Choice214U D)
  s21_12aR34F3Q35 : S21_12aFR34F3Q35 D (Choice214U D)

variable {G : Type} [Group G] [Finite G]

section Setup

theorem Steps87.toSteps86 (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hKA : KLieBorelAutPrime) (hU7T : PartTwo.Inputs1719.K_U7CentTorus)
    (hU7S : PartTwo.Inputs1719.K_U7CartanSylowAbelian)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hN : uc22p20rNativeGriess) (hK35w : UCK.K35w)
    (hKZ : PartOne.Section8.StronglyEmbeddedCentralFree) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree)
    (hB : BadNoStrongThree) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (Ch : Choice2011 G) (hKF7 : KF7Use (UC6.dataOfSetup4 hS hU S))
    (h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S))
    (hn3 : H1930 (UC6.dataOfSetup4 hS hU S) → ∀ c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch, 3 ≤ c.n)
    (h3 : S21_3 (UC6.dataOfSetup4 hS hU S) Ch) (h5 : S21_5 (UC6.dataOfSetup4 hS hU S) Ch)
    (h207 : S20_7 (UC6.dataOfSetup4 hS hU S)) (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S))
    (h211 : S21_1 (UC6.dataOfSetup4 hS hU S) Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → Ch L₀ B₀)
    (h : Steps87 (UC6.dataOfSetup4 hS hU S) Ch) : Steps86 (UC6.dataOfSetup4 hS hU S) Ch where
  s21_3Rest14 := s21_3Rest14_of_rest15 hGA hK35w hKZ hS hU S hMS hPart hSE hSS hK3 hB hOut Ch
    h.s21_3Rest15
  s21_14R4 := s21_14R4_setup4_of_residuals hGA hN hKA hS hU S hPart Ch hn3 h3 h5 h.s21_14R4F
  s21_14R3U := s21_14R3U_setup4_of_residuals hGA hS hU S hPart Ch h76 hn3 h3 h5 h.s21_14R3UF
    hU7T hU7S
  s21_14R3L := h.s21_14R3L
  s21_12aR34L3 := s21_12aFR34L3_of_l3P_l3E hKF1 hKS hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    hKF7 hn3 h5 h82 h211 hCh h.s21_12aR34L3P h.s21_12aR34L3E
  s21_12aR34F2 := s21_12aFR34F2_of_cases hKF1 hKS hKC hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S)
    hKF7 hn3 h5 h82 h211 hCh h.s21_12aR34F2Q35 h.s21_12aR34F2Sig h.s21_12aR34F2Even
  s21_12aR34F3 := s21_12aFR34F3_dataOfSetup4 hGA hS hU S hCh hKF7 h5 h207 h82 h211
    (PartTwo.Inputs1719.k_FunCommute_of_funHypOmega PartTwo.Inputs1719.k_FunHypOmega_holds) hKF1
    hKC hKS h.s21_12aR34F3Q35

end Setup

end CFSG.LocalAnalysis.UniquenessCase.UC22
