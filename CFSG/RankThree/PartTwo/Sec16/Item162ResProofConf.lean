module

public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofCA
public import CFSG.RankThree.PartTwo.Sec16.Item162ResProofTools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

theorem partTwoE_maximal {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) :
    ∀ E ∈ partTwoE G, ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := by
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  exact fun E hE B hB hEB => (hFE ▸ hE : E ∈ partTwoF G).2.1 B hB hEB

theorem sectionCentralizer_eq_zpowers_of_meetsY4 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hm : MeetsY4 A (lB A) L Y) (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) :
    Late.sectionCentralizer A Y (CFSG.Open.pCoreOf 2 Y) = (Subgroup.zpowers c : Set G) := by
  have hD := h.toSec13Data
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  obtain ⟨X, hX, hXLY⟩ := hm
  have hcsc := mem_sectionCentralizer_of_meets hD.isElemAbelian hD.mem_A hAY φ hX
    (hXLY.trans inf_le_right) ((hXLY.trans inf_le_left).trans hD.le_centralizer)
  exact sectionCentralizer_eq_zpowers_of_mem (partTwoE_maximal h) hD.isElemAbelian hAY
    hY.prop.2.2 φ hcsc hD.ne_one

end CFSG.RankThree.PartTwo.Sec16.Res162
