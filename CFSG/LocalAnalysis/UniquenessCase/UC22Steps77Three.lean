module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Steps76Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251t
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps77Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_14 : S21_14 D Ch
  s22_5_1RStarSn : S22_5_1RStarSn D Ch
  s21_12aR34L3P : S21_12aFR34L3P D (Choice214U D)
  s21_12aR34F2Q35 : S21_12aFR34F2Q35 D (Choice214U D)
  s21_12aR34F2Even : S21_12aFR34F2Even D (Choice214U D)
  r8_2 : F08.R82 D
  r8_69NRest3 : F08.R869NRest3 D
  r8_69MConsRest3 : F08.R869MConsRest3 D
  r8_80J4 : F08.R880J4 D
  s21_22R3F3SzQ5T : S21_22R3F3SzQ5T D Ch
  s21_22R3E5R : S21_22R3E5R D Ch
  s21_22R3NoPairR : S21_22R3NoPairR D Ch

section Certified


theorem Steps77Three.toSteps76Three {hS : RankThreeUC.Standing G} {S : RankThreeUC.Setup G}
    {Ch : Choice2011 G} (h : Steps77Three (PartTwo.Three.dataOfSetup hS S) Ch)
    (hx : DataExt (PartTwo.Three.dataOfSetup hS S))
    (h61 : UC6.R6_1 (PartTwo.Three.dataOfSetup hS S))
    (h119 : R119W (PartTwo.Three.dataOfSetup hS S))
    (h17 : S21_17 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h2112 : S21_12 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h31 : S22_3_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h33 : S22_3_3 (PartTwo.Three.dataOfSetup hS S) Ch)
    (hn3 : H1930 (PartTwo.Three.dataOfSetup hS S) →
      ∀ c : Ctx21 (PartTwo.Three.dataOfSetup hS S) Ch, 3 ≤ c.n)
    (hSg : UC6S846.SigmaStd (PartTwo.Three.dataOfSetup hS S))
    (h847 : R847E3L3 (PartTwo.Three.dataOfSetup hS S))
    (h920 : PartOne.Section9.R920odd (PartTwo.Three.dataOfSetup hS S))
    (h923 : F09.R923 (PartTwo.Three.dataOfSetup hS S))
    (h8107 : F08.R8107 (PartTwo.Three.dataOfSetup hS S))
    (h16 : S21_16 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h2014 : S20_14N (PartTwo.Three.dataOfSetup hS S))
    (hKF1 : KFieldAutOdd) (hKS : KFunSplit) (hKC : KFunCount)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hUC : CFSG.Open.rankThreeUC G)
    (hKF7 : KF7Use (PartTwo.Three.dataOfSetup hS S))
    (h5 : S21_5 (PartTwo.Three.dataOfSetup hS S) Ch)
    (hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (PartTwo.Three.dataOfSetup hS S) L₀ B₀ → Ch L₀ B₀) :
    Steps76Three (PartTwo.Three.dataOfSetup hS S) Ch where
  s21_14 := h.s21_14
  s22_5_1RStar := s22_5_1RStar_of_sn _ Ch hx h61 h119 h17 h211 h2112 h31 h33 hn3 hSg h847 h920
    h923 h8107 h16 h2014 h.s22_5_1RStarSn
  s21_12aR34L3P := h.s21_12aR34L3P
  s21_12aR34F2 := s21_12aFR34F2_dataOfSetup_of_q35_even hKF1 hKS hKC hGA hS hUC S hKF7 hn3 h5
    h.r8_2 h211 hCh h.s21_12aR34F2Q35 h.s21_12aR34F2Even
  r8_2 := h.r8_2
  r8_69NRest3 := h.r8_69NRest3
  r8_69MConsRest3 := h.r8_69MConsRest3
  r8_80J4 := h.r8_80J4
  s21_22R3F3SzQ5T := h.s21_22R3F3SzQ5T
  s21_22R3E5R := h.s21_22R3E5R
  s21_22R3NoPairR := h.s21_22R3NoPairR

end Certified

end Reduction

end CFSG.LocalAnalysis.UniquenessCase.UC22
