module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSp
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG.Open (StatedSp)

theorem spMarkedYcode_holds : SpMarkedYcode := by
  intro K _ _ _ ζ m hK hζ c hc
  cases c with
  | zero S =>
    have hS : 2 ≤ S.card := hc
    obtain ⟨e⟩ := nonempty_blockGroup_zero_mulEquiv ζ m hK hζ
      (Finset.card_pos.mp (show 0 < S.card by omega))
    change CFSG.StandardType.LargeEvenMarking
      ↥⁅blockGroup ζ m (.zero S), blockGroup ζ m (.zero S)⁆
      (fun lab _ _ _ _ _ => lab = if S.card = 2 then ⟨.B2der, 0, 1⟩ else ⟨.C, S.card, 1⟩)
    by_cases h2 : S.card = 2
    · rw [if_pos h2]
      revert e
      rw [h2]
      exact largeEvenMarking_commutator_of_mulEquiv_statedSp_two hK
    · rw [if_neg h2]
      exact largeEvenMarking_commutator_of_mulEquiv_statedSp hK (by omega) e
  | extension e =>
    obtain ⟨he, h4⟩ := hc
    obtain ⟨E, _, _, _, hE, ⟨φ⟩⟩ := exists_blockGroup_extension_mulEquiv ζ m hK hζ he
    exact largeEvenMarking_commutator_of_mulEquiv_guFull hE h4 φ

end CFSG.StandardType.GGQ2Frame.SpBlocks
