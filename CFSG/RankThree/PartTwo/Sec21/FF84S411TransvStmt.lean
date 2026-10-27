module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def A_transvRank_stmt : Prop :=
  ∀ Y : Subgroup P8, (Y = Ua ∨ Y = Ub) → ∀ x ∈ Y, x ≠ 1 → x ∉ ⁅Y, Subgroup.zpowers cc⁆ →
    x ∉ Y ⊓ Cen cc → ∀ A : Subgroup P8, A ≤ Op 2 (Cen x ⊓ A8s) → IsElementaryAbelian 2 A →
      Nat.card A ≤ 8

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
