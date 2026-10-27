module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Ree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34LFThree
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]


theorem s21_12aFR34F2_dataOfSetup_of_q35_even (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hKC : KFunCount) (hGA : GriessAllModelsStatement) (hS : Standing G) (hUC : rankThreeUC G)
    (S : Setup G) {Ch : Choice2011 G} (hKF7 : KF7Use (dataOfSetup hS S))
    (hn3 : H1930 (dataOfSetup hS S) → ∀ c : Ctx21 (dataOfSetup hS S) Ch, 3 ≤ c.n)
    (h5 : S21_5 (dataOfSetup hS S) Ch) (h82 : F08.R82 (dataOfSetup hS S))
    (h211 : S21_1 (dataOfSetup hS S) Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (dataOfSetup hS S) L₀ B₀ → Ch L₀ B₀)
    (hQ : S21_12aFR34F2Q35 (dataOfSetup hS S) (Choice214U (dataOfSetup hS S)))
    (hEv : S21_12aFR34F2Even (dataOfSetup hS S) (Choice214U (dataOfSetup hS S))) :
    S21_12aFR34F2 (dataOfSetup hS S) (Choice214U (dataOfSetup hS S)) :=
  s21_12aFR34F2_of_cases hKF1 hKS hKC hGA (UC6S846.sigmaStd_dataOfSetup hS S) hKF7 hn3 h5 h82
    h211 hCh hQ (s21_12aFR34F2Sig_dataOfSetup hS hUC S) hEv

theorem s21_12aFR34_dataOfSetup_of_l3P_q35_even (hKF1 : KFieldAutOdd) (hKS : KFunSplit)
    (hKC : KFunCount) (hGA : GriessAllModelsStatement) (hS : Standing G) (hUC : rankThreeUC G)
    (S : Setup G) {Ch : Choice2011 G} (hKF7 : KF7Use (dataOfSetup hS S))
    (hn3 : H1930 (dataOfSetup hS S) → ∀ c : Ctx21 (dataOfSetup hS S) Ch, 3 ≤ c.n)
    (h5 : S21_5 (dataOfSetup hS S) Ch) (h82 : F08.R82 (dataOfSetup hS S))
    (h211 : S21_1 (dataOfSetup hS S) Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (dataOfSetup hS S) L₀ B₀ → Ch L₀ B₀)
    (hP : S21_12aFR34L3P (dataOfSetup hS S) (Choice214U (dataOfSetup hS S)))
    (hQ : S21_12aFR34F2Q35 (dataOfSetup hS S) (Choice214U (dataOfSetup hS S)))
    (hEv : S21_12aFR34F2Even (dataOfSetup hS S) (Choice214U (dataOfSetup hS S))) :
    S21_12aFR34 (dataOfSetup hS S) (Choice214U (dataOfSetup hS S)) :=
  s21_12aFR34_of_rest hGA h82 h211 hCh (s21_12aFR34L3_dataOfSetup_of_l3P hS S hP)
    (s21_12aFR34F2_dataOfSetup_of_q35_even hKF1 hKS hKC hGA hS hUC S hKF7 hn3 h5 h82 h211 hCh hQ
      hEv)
    (s21_12aFR34F3_dataOfSetup hS S)

end CFSG.LocalAnalysis.UniquenessCase.UC22
