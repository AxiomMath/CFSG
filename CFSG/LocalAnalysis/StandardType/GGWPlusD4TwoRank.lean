module

public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoInnerSC
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoEquivSC
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoSC
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4CardOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem card_eq_pow_four_of_omegaPlus_two
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hP : GGTableBPosition 3 L' E
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) θ hE) :
    Nat.card E = 3 ^ 4 * Nat.card (E ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  obtain ⟨hZ, hcp⟩ :=
    OrthNs.center_data_omegaPlus (K := K) hp hp2 (by norm_num : 3 ≤ 4)
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker : (ggQuotHom θ).ker ≤ Subgroup.center L' := by rw [ker_ggQuotHom]
  have hperf : commutator L' = ⊤ := hP.1
  have hA : IsElemAbelian 3 (ggGamma L' hE).range := TableBBridge.isElemAbelian_range_gamma hP
  have hAI : ∀ a ∈ (ggGamma L' hE).range,
      ∃ φ ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))),
        ∀ l : ↥L', φ (ggQuotHom θ l) = ggQuotHom θ (a l) := TableBBridge.induces_range_gamma hP
  have hSC : GGTorusSelfCent 3 (ggGamma L' hE).range := TableBBridge.ggTorusSelfCent_range hP
  obtain ⟨E₁, hE₁ab, hE₁card, hE₁sc⟩ :=
    exists_sc_subgroup_of_selfCent hp hZ hcp L' (ggQuotHom θ) hψ hker hperf hA hAI hSC
  obtain ⟨E₂, hE₂ab, hE₂card, hE₂sc⟩ :=
    exists_sc_subgroup_of_mulEquiv
      (RecipeFieldOmega.plusEquiv (K := K) (m := 4) (by norm_num : 1 ≤ 4)) hE₁ab hE₁sc
  have hcard₂ : Nat.card E₂ = Nat.card (ggGamma L' hE).range := hE₂card.trans hE₁card
  have h27 : 27 ≤ Nat.card (ggGamma L' hE).range := by
    have h := TableBBridge.pow_three_le_card_range hP hp
    rwa [show (3 : ℕ) ^ 3 = 27 by norm_num] at h
  have h81 : 81 ≤ Nat.card (ggGamma L' hE).range := by
    have h := ggOmegaPlusEight_sc_card hK hE₂ab hE₂sc (by rw [hcard₂]; exact h27)
    rwa [hcard₂] at h
  have hle : Nat.card (ggGamma L' hE).range ≤ 3 ^ 4 :=
    card_le_pow_orthPlus_cover (by norm_num : 1 ≤ 4) hp hp2 hZ L' (ggQuotHom θ) hψ hker hperf
      hA hAI
  have hcardA : Nat.card (ggGamma L' hE).range = 3 ^ 4 := by
    refine le_antisymm hle ?_
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num]
    exact h81
  rw [TableBBridge.card_eq_card_range_mul hE, hcardA]

end CFSG.StandardType
