module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35CE
public import CFSG.RankThree.PartTwo.KFacts.KS163U35Klein
import CFSG.RankThree.PartTwo.Sec16.Item163U35Y
import CFSG.RankThree.PartTwo.Sec16.Item163U35Zeta
import CFSG.RankThree.PartTwo.Sec16.Item163U35Pair
import CFSG.RankThree.PartTwo.Sec16.Item163U35Step3
import CFSG.RankThree.PartTwo.Sec16.Item163U35Step5
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

namespace Proof163U35

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y : Subgroup G}

namespace Conf684

theorem inf_ne_left_of_maxCE684 (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    {K₁ K₂ T₁ T₂ : Subgroup G} (hmax : MaxCE684 A L K₁ K₂ T₁ T₂) : T₁ ⊓ T₂ ≠ T₁ := by
  intro heq
  have hle : T₁ ≤ T₂ := inf_eq_left.mp heq
  have hT : T₁ = T₂ := le_antisymm hle
    ((h.mem_top_of_isZeta hmax.1.zeta₁).2 (h.mem_top_of_isZeta hmax.1.zeta₂).prop hle)
  have hK : K₁ = K₂ := h.eq_of_isZeta hK1 hmax.1.zeta₁ (by rw [hT]; exact hmax.1.zeta₂)
  exact hmax.1.not_conj ⟨1, one_mem _, by rw [Late.map_conj_one]; exact hK⟩

theorem inf_ne_right_of_maxCE684 (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    {K₁ K₂ T₁ T₂ : Subgroup G} (hmax : MaxCE684 A L K₁ K₂ T₁ T₂) : T₁ ⊓ T₂ ≠ T₂ := by
  have h' := h.inf_ne_left_of_maxCE684 hK1 hmax.symm
  rwa [inf_comm] at h'

theorem false_of_mem (h : Conf684 A c L Y) (hK1 : KFacts.KS163U35InvTwo)
    (hK2 : KFacts.KS163U35KleinGen) {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hwL : w ∈ L) (hwN : w ∉ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G)) : False := by
  obtain ⟨K₁, K₂, T₁, T₂, hce⟩ := h.exists_ce684 hwA hwL hwN
  obtain ⟨K₁, K₂, T₁, T₂, hmax⟩ := exists_maxCE684 hce
  have hne₁ := h.inf_ne_left_of_maxCE684 hK1 hmax
  have hne₂ := h.inf_ne_right_of_maxCE684 hK1 hmax
  exact h.false_of_maxCE684_of_not_le hK2 hmax (h.not_le_left_of_maxCE684 hmax hne₁ hne₂)
    (h.not_le_right_of_maxCE684 hmax hne₁ hne₂)

end Conf684

end Proof163U35

end CFSG.RankThree.PartTwo.Sec16
