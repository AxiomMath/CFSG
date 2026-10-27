module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSL3E27
import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofNF
import CFSG.RankThree.PartTwo.Sec21.Item228Insp2ProofGenB

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Item228Insp2Proof

theorem sl3E27 : SL3E27 := by
  intro G _ _ X A m hm0 hme ⟨eX⟩ hAe hA27 hAX hAX9 hC3 hfield
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_three hm0 hme
  obtain ⟨ι, hTA, hT, hact⟩ := exists_normalForm hm0 hme eX hAe hAX hAX9 hfield hω
  have h2 : (2 : GaloisField 2 m) = 0 := CharTwo.two_eq_zero
  refine ⟨nonempty_starOf_equiv_perm h2 hω hAX ι hTA hT hact, ?_⟩
  have hN : IsNormalForm A hAX ι := ⟨hTA, hT, hact⟩
  have hK4 : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m hm0.ne']
    obtain ⟨k, hk⟩ := hme
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro B₁ B₂ P₁ P₂ hB₁ hB₂ h9₁ h9₂ hne hP₁ hP₂ ⟨e₁⟩ ⟨e₂⟩
  exact sup_eq_of_normalForm hK4 hω hN hAe hA27 hAX9 hC3 B₁ B₂ P₁ P₂ hB₁ hB₂ h9₁ h9₂ hne hP₁ hP₂
    ⟨e₁.trans (projSLTwoEquivSL _)⟩ ⟨e₂.trans (projSLTwoEquivSL _)⟩

end CFSG.RankThree.PartTwo.Sec21
