module

public import CFSG.GH74.Generic.GKFTables
public import CFSG.Adapters.TauCetiExceptional.BridgeG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup TauCeti CFSG.Blueprint.Multiplier
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)


theorem lieModel_of_chevalleyExceptionalModel_G2_three {G : Type} [Group G]
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 3 1) :
    CFSG.Models.LieModel G .G2 0 3 1 := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hM
  let q : PrimePower := ⟨3, 1, Nat.prime_three, one_pos⟩
  have hq : q.card = 3 := by rw [PrimePower.card_def]; rfl
  have hv : (LieTypeIndex.G2 q).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · rw [LieTypeIndex.inStandardRange_iff]
      exact hq.symm.le
    · simp [LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv (by decide) K
    (by rw [hK, hq]; norm_num)
  exact ⟨hadm, Or.inr ⟨rfl, ⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩⟩

theorem card_center_dvd_three_of_G2 (hGA : GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : IsQuasisimple X)
    (hM : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ center X) .G2 3 1) :
    Nat.card (center X) ∣ 3 := by
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hX (MulEquiv.refl _)
  rw [CFSG.GH74.Generic.card_hopfMultiplier_of_griess hGA
    (lieModel_of_chevalleyExceptionalModel_G2_three hM)] at h
  simpa [genericOrders, exceptionalOrders] using h

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
