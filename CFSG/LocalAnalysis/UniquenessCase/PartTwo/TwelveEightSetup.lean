module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

namespace TwelveEightSetup

theorem uniqueMaxLocal_of_uniqueMax {M X : Subgroup G} (h : UniqueMax M X) :
    X ≤ M ∧ ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → X ≤ H → H = M := by
  have hM : M ∈ calMOf X := by rw [h]; exact Set.mem_singleton M
  refine ⟨hM.2, fun H hH hXH => ?_⟩
  have hH' : H ∈ calMOf X := ⟨hH, hXH⟩
  rw [h] at hH'
  exact hH'

theorem ne_bot_of_not_isTI {V : Subgroup G} (h : ¬ IsTI V) : V ≠ ⊥ := by
  rintro rfl
  exact h fun g => Or.inl (bot_inf_eq _)

theorem exists_not_isTI_ofSetup (hS : Standing G) (S : Setup G) :
    ∃ V : Subgroup G, InCalV (Three.dataOfSetup hS S).M V ∧ ¬ IsTI V := by
  exact ⟨S.V, ⟨ne_bot_of_not_isTI S.not_isTI, S.le, S.le_normalizer, S.elemAbelian⟩,
    S.not_isTI⟩

theorem exists_not_isTI_ofSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) :
    ∃ V : Subgroup G, InCalV (UC6.dataOfSetup4 hS hU S).M V ∧ ¬ IsTI V := by
  exact ⟨S.V, ⟨ne_bot_of_not_isTI S.not_isTI, S.le, S.le_normalizer, S.elemAbelian⟩,
    S.not_isTI⟩

end TwelveEightSetup

theorem twelve_eight_emptyW_ofSetup (hS : Standing G) (_hUC : rankThreeUC G) (S : Setup G)
    (_hMS : S.InMSigma) (h1214 : F12.R1214 (Three.dataOfSetup hS S))
    (h124 : ∃ H₀ ∈ hSet S.T S.M, Hyp124 S.M H₀)
    (hW : ∀ W : Subgroup G, ¬ ((InCalV S.M W ∧
      (S.M ⊓ normalizer ((S.T ⊓ centralizer (W : Set G) : Subgroup G) : Set G) ≤ S.M ∧
        ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H →
          S.M ⊓ normalizer ((S.T ⊓ centralizer (W : Set G) : Subgroup G) : Set G) ≤ H →
            H = S.M)) ∧ 8 ≤ Nat.card W ∧ TwoReduced S.M W)) :
    ∃ V₀ V : Subgroup G, InCalV0 S.M V₀ V ∧ CentralizersUnique S.M S.T := by
  have hx : DataExt (Three.dataOfSetup hS S) := dataExt_ofSetup hS S
  have h61 : UC6.R6_1 (Three.dataOfSetup hS S) := Three.r6_1_dataOfSetup hS S
  have hW' : ∀ W : Subgroup G,
      ¬ InCalW (Three.dataOfSetup hS S).M (Three.dataOfSetup hS S).T W := fun W hWin =>
    hW W ⟨⟨hWin.1.1, TwelveEightSetup.uniqueMaxLocal_of_uniqueMax hWin.1.2⟩, hWin.2.1,
      hWin.2.2⟩
  obtain ⟨V₀, V, h0⟩ := TwelveEight.exists_inCalV0 _ hx h61 h1214 h124
    (TwelveEightSetup.exists_not_isTI_ofSetup hS S) hW'
  exact ⟨V₀, V, h0, TwelveEight.centralizersUnique _ (TwelveEight.isTI_U _ hx h61 hW')⟩

theorem twelve_eight_ofSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (h1214 : F12.R1214 (UC6.dataOfSetup4 hS hU S))
    (h124 : ∃ H₀ ∈ hSet S.T S.M, Hyp124 S.M H₀) :
    ∃ V₀ V : Subgroup G, Hyp125 (UC6.dataOfSetup4 hS hU S) V₀ V := by
  exact twelve_eight_of_exists_not_isTI _ (dataExt_ofSetup4 hS hU S)
    (UC6.r6_1_dataOfSetup4 hS hU S) h1214
    (TwelveEightSetup.exists_not_isTI_ofSetup4 hS hU S) h124

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
