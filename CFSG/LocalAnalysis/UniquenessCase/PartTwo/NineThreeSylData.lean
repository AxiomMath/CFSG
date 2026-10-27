module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_top_and_normalizer_le (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) :
    IsSylowIn 2 D.T ⊤ ∧ normalizer (D.T : Set G) ≤ normalizer (V : Set G) :=
  ⟨TwelveShort.isSylowIn_of_le D le_top,
    (normalizer_eq_of_inCalV D hV).symm ▸ D.normalizer_le⟩

theorem thm93_of_thm93Syl (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (h : WeakClosure81.Thm93Syl V D.T) : WeakClosure81.Thm93 V D.T :=
  h.thm93 (isSylowIn_top_and_normalizer_le D hV).1 (isSylowIn_top_and_normalizer_le D hV).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
