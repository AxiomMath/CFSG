module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNorm
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalIrr
import CFSG.Sporadic.J4
import CFSG.Mathlib.GroupTheory.ExtraspecialLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8


theorem k335SporNormAt_J4 : K335SporNormAt .J4 := by
  intro X _ _ hX S Q hS hQS hQ
  obtain ⟨e⟩ := hX
  obtain ⟨x, y, h, hx, hy, -, hzx, hzy, hcard, hhx, hhy, -⟩ :=
    CFSG.SectionRank.J4_sylow3_irr_cubic_witness
  have hn : (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 := by norm_num
  exact CFSG.Extraspecial.exists_normalizer_not_mem_of_mulEquiv e hx hy hzx hzy hcard
    (CFSG.Sporadic.J4.card_J4.trans hn) (by norm_num) hhx hhy (by decide) S Q hS hQS hQ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
