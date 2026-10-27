module

public import CFSG.Blueprint.Catalog
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open TauCeti

theorem suzukiModel_of_index (m : ℕ) (hm : (LieTypeIndex.suzuki m).Valid) :
    Blueprint.SuzukiModel (CFSGIndex.lie ⟨.suzuki m, hm⟩).Group 2 (2 * m + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hm).1
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  exact ⟨rfl, m, hm1, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, rfl, hK,
    ⟨(CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hm).trans
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm⟩⟩

end CFSG.RankThree.PartTwo.Sec4.Census
