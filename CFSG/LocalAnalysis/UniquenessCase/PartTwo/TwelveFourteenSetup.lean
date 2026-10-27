module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteen
import CFSG.LocalAnalysis.UniquenessCase.UC611f
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)

variable {G : Type} [Group G] [Finite G]

namespace TwelveFourteenSetup

theorem isStronglyPEmbedded_of_three_mem_sig1 (hS : Standing G) (S : Setup G)
    (h3 : 3 ∈ (Three.dataOfSetup hS S).sig1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (Three.dataOfSetup hS S).M := by
  obtain ⟨hq, Q, hw, hΓ⟩ := h3
  exact (IsWitness.gamma_one_le_iff hS hq hw).1 hΓ

theorem three_not_mem_sig2 (hS : Standing G) (S : Setup G) :
    3 ∉ (Three.dataOfSetup hS S).sig2 := by
  rintro ⟨-, Q, -, h5, -⟩
  omega

theorem exists_not_isTI (hS : Standing G) (S : Setup G) :
    ∃ V : Subgroup G, InCalV (Three.dataOfSetup hS S).M V ∧ ¬ IsTI V := by
  refine ⟨S.V, ⟨?_, S.le, S.le_normalizer, S.elemAbelian⟩, S.not_isTI⟩
  intro h
  apply S.not_isTI
  rw [h]
  exact fun g => Or.inl (bot_inf_eq _)

theorem isStronglyPEmbedded_of_three_mem_sig1_four (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∈ (UC6.dataOfSetup4 hS hU S).sig1) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 (UC6.dataOfSetup4 hS hU S).M := by
  have hp : 3 ∈ uniqueFourSigma S.M := h3.1
  obtain ⟨-, hM0, -, P, -, -, hcl⟩ := (hU S.M S.maxLocal ⟨3, hp⟩).1 3 hp
  rcases hcl with ⟨hdvd, hstrong⟩ | ⟨h5, -⟩
  · exact UC6.isStronglyPEmbedded_of_clause_one hM0 hdvd hstrong
  · omega

theorem three_not_mem_sig2_four (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) : 3 ∉ (UC6.dataOfSetup4 hS hU S).sig2 := by
  rintro ⟨-, -, M', -, -, P, -, -, h5, -⟩
  omega

theorem r6_11_four (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) :
    UC6.R6_11 (UC6.dataOfSetup4 hS hU S) := by
  intro h3
  exact absurd h3 (Set.notMem_empty 3)

theorem exists_not_isTI_four (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) :
    ∃ V : Subgroup G, InCalV (UC6.dataOfSetup4 hS hU S).M V ∧ ¬ IsTI V := by
  refine ⟨S.V, ⟨?_, S.le, S.le_normalizer, S.elemAbelian⟩, S.not_isTI⟩
  intro h
  apply S.not_isTI
  rw [h]
  exact fun g => Or.inl (bot_inf_eq _)

end TwelveFourteenSetup

theorem r1214_ofSetup_of_r126 (hS : Standing G) (S : Setup G)
    (h126 : R126 (Three.dataOfSetup hS S))
    (h127 : R127 (Three.dataOfSetup hS S)) (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) : F12.R1214 (Three.dataOfSetup hS S) := by
  exact r1214_of_twelve_fourteen _ (dataExt_ofSetup hS S) (Three.r6_1_dataOfSetup hS S)
    (UC6.r6_11Used_dataOfSetup hS S)
    (TwelveFourteenSetup.isStronglyPEmbedded_of_three_mem_sig1 hS S)
    (TwelveFourteenSetup.three_not_mem_sig2 hS S) (TwelveFourteenSetup.exists_not_isTI hS S)
    h126 h127 h861 hTim S.notCatalog

theorem r1214_ofSetup4_of_r126 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (h126 : R126 (UC6.dataOfSetup4 hS hU S)) (h127 : R127 (UC6.dataOfSetup4 hS hU S))
    (h861 : W3Lem86_1 G) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) :
    F12.R1214 (UC6.dataOfSetup4 hS hU S) := by
  exact r1214_of_twelve_fourteen _ (dataExt_ofSetup4 hS hU S) (UC6.r6_1_dataOfSetup4 hS hU S)
    (UC6.r6_11Used_of_r6_11 (TwelveFourteenSetup.r6_11_four hS hU S))
    (TwelveFourteenSetup.isStronglyPEmbedded_of_three_mem_sig1_four hS hU S)
    (TwelveFourteenSetup.three_not_mem_sig2_four hS hU S)
    (TwelveFourteenSetup.exists_not_isTI_four hS hU S) h126 h127 h861 hTim S.notCatalog

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
