module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEightSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenBAS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenSetupAS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem twelve_eight_emptyW_ofSetup_of_inputs_AS (hS : Standing G)
    (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (h5_11 : WeakClosure81.Asch5_11AS)
    (h5_13 : WeakClosure81.Asch5_13AS) (h861 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (h93 : ∀ V T : Subgroup G, WeakClosure81.Thm93Syl V T)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (S : Setup G) (hMS : S.InMSigma)
    (h124 : ∃ H₀ ∈ hSet S.T S.M, Hyp124 S.M H₀)
    (hW : ∀ W : Subgroup G, ¬ CFSG.Yardstones.Me2c15c2c995a.InCalW S.M S.T W) :
    ∃ V₀ V : Subgroup G, CFSG.Yardstones.Me2c15c2c995a.InCalV0 S.M V₀ V ∧
      CFSG.Yardstones.Me2c15c2c995a.CentralizersUnique S.M S.T := by
  have h63 := Three.r6_3_dataOfSetup hS hUC hC S
  have h66 := Three.r6_6_dataOfSetup hS hUC hC S
  have h127 : R127 (Three.dataOfSetup hS S) :=
    r127_of_twelve_seven_AS_syl hTim S.notCatalog _ h5_11 h5_13 h63 h66 h861 h88 fun V => h93 V _
  have h1214 := r1214_ofSetup_AS hS hUC hC S h5_11 h5_13 h127 h861 hTim
  exact twelve_eight_emptyW_ofSetup hS hUC S hMS h1214 h124 hW

theorem ascTwelveEightEmptyW_of_inputs_AS
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h861 : ∀ (G : Type) [Group G] [Finite G], W3Lem86_1 G)
    (h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) :
    CFSG.Yardstones.Me2c15c2c995a.AscTwelveEightEmptyW := by
  intro G _ _ hS hUC S hMS h124 hW
  exact twelve_eight_emptyW_ofSetup_of_inputs_AS hS hUC (hC G hS) h5_11 h5_13 (h861 G) (h88 G)
    (h93 G) hTim S hMS h124 hW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
