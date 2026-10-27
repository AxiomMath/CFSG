module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNorm
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
import CFSG.Sporadic.Ru
import CFSG.Mathlib.GroupTheory.ExtraspecialLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8


theorem k335SporNormAt_Ru : K335SporNormAt .Ru := by
  intro X _ _ hX S Q hS hQS hQ
  obtain ⟨e⟩ := hX
  obtain ⟨x, y, h, hx, hy, -, hzx, hzy, hcard, hhx, hhy, -⟩ :=
    CFSG.SectionRank.Ru_sylow3_cubic_witness
  have hn : (145926144000 : ℕ) = 3 ^ 3 * 5404672000 := by norm_num
  exact CFSG.Extraspecial.exists_normalizer_not_mem_of_mulEquiv e hx hy hzx hzy hcard
    (CFSG.Sporadic.Ru.card_Ru.trans hn) (by norm_num) hhx hhy (by decide) S Q hS hQS hQ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
