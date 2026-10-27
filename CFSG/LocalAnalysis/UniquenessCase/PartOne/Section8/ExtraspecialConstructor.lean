module

public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.CommutatorCentre

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup

theorem isExtraspecialExpP_three_of_card_exponent_center
    {Q : Type} [Group Q] [Finite Q]
    (hcard : Nat.card Q = 27) (hexp : Monoid.exponent Q = 3)
    (hcenter : Nat.card (Subgroup.center Q) = 3) :
    CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 Q := by
  have hpow : Nat.card Q = 3 ^ (1 + 2 * 1) := by simpa using hcard
  have hcomm : commutator Q = Subgroup.center Q :=
    CFSG.AGLEmbeddingD2.Wilson.Proving.commutator_top_eq_center_of_card
      Nat.prime_three hcard hcenter
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
  exact ⟨hpow, hexp, hcomm, hcenter⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
