module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNorm
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.Sporadic.Mathieu.M24
import CFSG.Mathlib.GroupTheory.ExtraspecialLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8


theorem k335SporNormAt_M24 : K335SporNormAt .M24 := by
  intro X _ _ hX S Q hS hQS hQ
  obtain ⟨e⟩ := hX
  obtain ⟨x, y, h, hx, hy, -, hzx, hzy, hcard, hhx, hhy, -⟩ :=
    CFSG.SectionRank.M24_sylow3_cubic_witness
  have hn : (244823040 : ℕ) = 3 ^ 3 * 9067520 := by norm_num
  exact CFSG.Extraspecial.exists_normalizer_not_mem_of_mulEquiv e hx hy hzx hzy hcard
    (CFSG.Sporadic.Mathieu.card_M24.trans hn) (by norm_num) hhx hhy (by decide) S Q hS hQS hQ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
