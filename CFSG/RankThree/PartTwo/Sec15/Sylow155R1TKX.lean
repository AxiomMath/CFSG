module

public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptY4_of_le_delta (h135 : Item135) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hLΔ : L ≤ delta A (lB A) L) : L ∈ scriptY4 A (lB A) := by
  have hD := hR.toSec13Data
  have hLtop : L ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hR.toTheoremFourHyp
    hD.ne_one (top_le_iff.mp (htop ▸ hD.le_centralizer))
  exact ⟨⟨hLtop, hD.le_normalizer⟩, Sec16.eq_oPrimeResidualOf_of_sec15R hR,
    le_antisymm hLΔ (delta_le L), h135 G A c L hD hR.hypS_or_hypT⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
