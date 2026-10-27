module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335HNorm
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.Sporadic.He
import CFSG.Mathlib.GroupTheory.ExtraspecialLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8


theorem k335SporNormAt_He : K335SporNormAt .He := by
  intro X _ _ hX S Q hS hQS hQ
  obtain ⟨e⟩ := hX
  obtain ⟨x, y, h, hx, hy, -, hzx, hzy, hcard, hhx, hhy, -⟩ :=
    CFSG.SectionRank.He_sylow3_cubic_witness
  have hn : (4030387200 : ℕ) = 3 ^ 3 * 149273600 := by norm_num
  exact CFSG.Extraspecial.exists_normalizer_not_mem_of_mulEquiv e hx hy hzx hzy hcard
    (CFSG.Sporadic.He.fam_he_order.1.trans hn) (by norm_num) hhx hhy (by decide) S Q hS hQS hQ

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
