module

public import CFSG.OddTranspositions.PartThree.Nine.Delta

public section

namespace CFSG.OddTranspositions.PartThree.Nine

theorem lemma9_4 : Lemma9_4 := by
  intro G _ _ D hC hH _ h3 T S hTS
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  have := hU.isElementaryAbelian
  have hΔ := hU.sylow_inter
  unfold Conclusion9_4
  refine ⟨by rw [hU.sylow_map_inter, hΔ],
    CFSG.OddTranspositions.PartThree.sylow_le_normalizer_inter hC.setup.isClass S, ?_, ?_⟩
  · rw [hΔ]
    exact hU.two_transitive
  · rw [hΔ]
    rcases hU.solvable_or_projective_seven h3 with ⟨hsolv, -⟩ | ⟨h8, he⟩
    · exact Or.inl hsolv
    · refine Or.inr ⟨?_, he⟩
      rw [Set.ncard_image_of_injective _ (mul_right_injective hC.d), ← Nat.card_coe_set_eq]
      exact h8

end CFSG.OddTranspositions.PartThree.Nine
