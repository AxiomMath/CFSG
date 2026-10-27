module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

@[expose] def KFSubL3 : Prop :=
  ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m →
  ∀ (H N : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)))),
    ⁅H, H⁆ = H → N ≤ H → ∀ [(N.subgroupOf H).Normal], IsPGroup 2 N →
    IsLThreeEpsAt (↥H ⧸ N.subgroupOf H) 2 n →
    (∀ U : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
        IsPGroup 2 U → H ≤ Subgroup.normalizer (U : Set ↥(CFSG.Assembly.RankThreeEven.projSL 3
          (GaloisField 2 (2 * n * m)))) → U = ⊥) ∧
    Subgroup.centralizer
      (H : Set ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)))) = ⊥ ∧
    (∀ α β : MulAut (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
        α ^ 2 = 1 → β ^ 2 = 1 → α ≠ 1 → β ≠ 1 → (∀ h ∈ H, α h = h) → (∀ h ∈ H, β h = h) →
          α = β) ∧
    (∀ β : MulAut (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
        β ^ 2 = 1 → β ≠ 1 → (∀ h ∈ H, β h = h) → ∃ j, (β j * j⁻¹) ^ 12 ≠ 1)

end CFSG.RankThree.PartTwo.Sec15.Ronan155R
