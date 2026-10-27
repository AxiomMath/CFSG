module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.StandardType.GGSixE6A24Centre
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index
import CFSG.LargeExtraspecial.A2ModOrdCard
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.Sporadic.Schreier.TitsIso
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section Levi

theorem isSimpleGroup_lE : IsSimpleGroup ↥lE := by
  unfold lE
  exact E6Pilot.isSimpleGroup_a5Levi (K := F2)

theorem card_lE : Nat.card ↥lE = ordA 5 2 := by
  have hmod : LieModel ↥lE .PSL 6 2 1 := by
    unfold lE
    exact E6Pilot.lieModel_a5Levi (K := F2) (f := 1) (GaloisField.card 2 1 (by norm_num))
  exact (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSL hmod).2

theorem card_EC : Nat.card EC = ordE6 2 := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6 (K := F2)
  have hcard : Nat.card F2 = 2 := by
    simpa using GaloisField.card 2 1 (by norm_num)
  change Nat.card (adjointGroup .E6 F2) = ordE6 2
  rw [h, hcard]

theorem finite_EC : Finite EC :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.finite_adjointGroup_E6 (K := F2)

theorem center_EC : Subgroup.center EC = ⊥ :=
  CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := F2)

theorem isSimpleGroup_EC : IsSimpleGroup EC := by
  have he : (EC ⧸ Subgroup.center EC) ≃* EC :=
    (QuotientGroup.quotientMulEquivOfEq center_EC).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (EC ⧸ Subgroup.center EC) :=
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 F2).2.1
  exact he.symm.isSimpleGroup

end Levi

end CFSG.StandardType.GGSixE6Two
