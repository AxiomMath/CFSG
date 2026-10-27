module

public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Centralizer
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClMark
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open

section Marking

theorem not_ggNbrClauseFiveMarking_of_lieModel_E8 {G : Type} [Group G] {K' : Subgroup G}
    {f p : ℕ} (hf : 1 ≤ f) (hX : LieModel (↥K' ⧸ Subgroup.center ↥K') .E8 0 2 f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1) {x : G}
    (hinn : ∃ k ∈ K', ∀ l ∈ K', x⁻¹ * l * x = k⁻¹ * l * k) : ¬ GGNbrClauseFiveMarking p x K' := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  refine ClNonsplit.not_ggNbrClauseFiveMarking_of_inner hp hp3 hinn
    (fun lab hlab hc hMM hHS => ?_) (fun lab hlab hc hMM => ?_)
  · obtain ⟨ht, hn⟩ := NbrInnerMore.eq_of_markedModel_E8 hf hX hlab hc hMM
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hn
    subst ht hn
    rcases NbrInnerMore.halfSplit_E8_cases hHS with h1 | h1 | ⟨-, h1⟩
    · exact hq1 h1
    · exact hq2 h1
    · exact hp3 h1
  · obtain ⟨ht, -⟩ := NbrInnerMore.eq_of_markedModel_E8 hf hX hlab hc hMM
    exact ggRawInnFieldOn_excInn p hp hp2 lab hlab (Or.inr (Or.inr ht))

theorem not_ggNbrClauseFiveMarking_of_isFiveB {G H : Type} [Group G] [Group H] {ψ : H →* G}
    (hψ : Function.Injective ψ) {y : H} {K₀ : Subgroup H} (h : IsFiveB y K₀) {x : G}
    (hinn : ∃ k ∈ K₀.map ψ, ∀ l ∈ K₀.map ψ, x⁻¹ * l * x = k⁻¹ * l * k) :
    ¬ GGNbrClauseFiveMarking 5 x (K₀.map ψ) := by
  have hF : Nat.card (GaloisField 2 1) = 2 ^ 1 := by
    rw [pow_one]
    exact GaloisField.card 2 1 one_ne_zero
  exact OmNonsplit.not_ggNbrClauseFiveMarking_of_omModel (f := 1) hF
    (OmNonsplit.OmModel.of_mulEquiv (K₀.equivMapOfInjective ψ hψ).symm h.2.2.2.2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hinn

end Marking

end FieldFiveE8

end CFSG.StandardType
