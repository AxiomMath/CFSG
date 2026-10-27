module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactWreathAbel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactWreathRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactWreathSec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem false_of_isL2_three_of_two_subgroups {Q : Type} [Group Q] [Finite Q]
    (hab : ∀ R : Subgroup Q, IsPGroup 2 ↥R →
      ∃ B : Subgroup Q, B ≤ R ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.relIndex R ≤ 2)
    (hrk : CFSG.Open.pRank 2 (⊤ : Subgroup Q) ≤ 2) {X : Subgroup Q}
    (hX : IsL2 (Bar2 X) 3) : False := by
  obtain ⟨T, E, _, _, π, σ, f, hT, hπ, hE, hE8, hσf, hirr⟩ := exists_section_of_isL2_three hX
  obtain ⟨B, hBT, hBab, hBidx⟩ := hab T hT
  refine false_of_irreducible_section_of_abelian_index_two π hπ hE hE8 σ f hσf hirr
    ⟨B.subgroupOf T, fun a ha b hb => Subtype.ext (hBab a ha b hb), hBidx⟩
    fun A hA => card_map_le_four_of_pRank_two_le_two hrk π hE hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
