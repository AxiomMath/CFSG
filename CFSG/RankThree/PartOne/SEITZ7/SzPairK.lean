module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Ree.Duality
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersKernel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.StronglyEmbedded.Catalog.Suzuki

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open TauCeti

theorem isoLie_suzuki_of_blueprint {A : Type} [Group A] {m : ℕ} (hm : 1 ≤ m) {X : Type} [Field X]
    [Finite X] (hX : Nat.card X = 2 ^ (2 * m + 1)) (e : A ≃* suzukiGroup m X) :
    IsoLie A (.suzuki m) := by
  have hv : (LieTypeIndex.suzuki m).Valid := by
    rw [LieTypeIndex.valid_iff]
    refine ⟨(LieTypeIndex.inStandardRange_iff _).2 hm, ?_⟩
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    exact fun h => h
  exact ⟨hv, ⟨(e.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
    hX)).trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

end CFSG.RankThree.PartOne.SEITZ7
