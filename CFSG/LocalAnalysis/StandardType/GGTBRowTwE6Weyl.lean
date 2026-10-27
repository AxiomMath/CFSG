module

public import CFSG.LocalAnalysis.StandardType.GGTBRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Frame
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcWeyl
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTwE6Row_weylOfType
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L) :
    GGWeylOfType p CoxeterMatrix.E₆ (ggAutomizer L Bs) := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection p Bs := hHyp.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := GGInnerDiagOn.le_normalizer hHyp.2.2.1.1
  have hZ : Nat.card ↥(Bs ⊓ L ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    card_bstar_inf_center_le hcfg
  exact ggWeylOfType_of_frame hp hp2 hBs hSC hNoTr hN hZ (ggTwE6Row_frame hHyp hL hN)

end CFSG.StandardType

end
