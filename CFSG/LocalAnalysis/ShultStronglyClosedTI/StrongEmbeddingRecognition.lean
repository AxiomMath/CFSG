module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryRecognition
public import CFSG.StronglyEmbedded.BenderNormalSeries

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank_two_strongEmbedding_involutionCore_recognition
    (hrank : TwoRankAtLeastTwo G) (H : Subgroup G)
    (hH : fusionStronglyEmbedded H) :
    Odd (involutionCore G).index ∧
      fusionIsBenderGroup (involutionCore G ⧸ (oddCore G).subgroupOf (involutionCore G)) ∧
      (oddCore G).subgroupOf (involutionCore G) ≠ ⊤ := by
  let L : Subgroup G := involutionCore G
  have hLrank : TwoRankAtLeastTwo L := twoRankAtLeastTwo_involutionCore_iff.mpr hrank
  have hnative := hH.to_native
  have hSE := theorem_SE H hnative
  rcases hSE with hlow | hB
  · exact (hlow hLrank).elim
  · have hOddL : oddCore L = (oddCore G).subgroupOf L := by
      apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      exact CFSG.ComponentClassification.OddCore.normal_intersection G L
    have hO : twoPrimeCore L = (oddCore G).subgroupOf L :=
      (oddCore_eq_twoPrimeCore (G := L)).symm.trans hOddL
    have hmodel : fusionIsBenderGroup (L ⧸ (oddCore G).subgroupOf L) := by
      apply fusionIsBenderGroup_of_isSimpleBenderGroup
      exact hB.1.map_mulEquiv (QuotientGroup.quotientMulEquivOfEq hO)
    have hnontrivial : (oddCore G).subgroupOf L ≠ ⊤ := by
      intro htop
      have hLle : L ≤ oddCore G := Subgroup.subgroupOf_eq_top.mp htop
      obtain ⟨a, _, _, _⟩ := rank_two_exists_commuting_involutions hLrank
      have hsquare : (a.val : G) ^ 2 = 1 :=
        congrArg Subtype.val (orderOf_eq_prime_iff.mp a.property).1
      have hone : (a.val : G) = 1 :=
        square_one_eq_one_of_mem_odd_subgroup (oddCore G)
          (CFSG.ComponentClassification.OddCore.odd_card G) (hLle a.val.property) hsquare
      exact (orderOf_eq_prime_iff.mp a.property).2 (Subtype.ext hone)
    exact ⟨hnative.involutionCore_index_odd_of_bender hB, hmodel, hnontrivial⟩

theorem rank_two_strongEmbedding_r1Full (hrank : TwoRankAtLeastTwo G)
    (H : Subgroup G) (hH : fusionStronglyEmbedded H) : R1Full G := by
  let L : Subgroup G := involutionCore G
  let R : Subgroup G := oddCore G
  let N : Subgroup G := L ⊔ R
  obtain ⟨hindex, hmodel, hnontrivial⟩ :=
    rank_two_strongEmbedding_involutionCore_recognition hrank H hH
  have hstrict : R < N := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro hRN
    have hLle : L ≤ R := hRN ▸ (le_sup_left : L ≤ N)
    exact hnontrivial (Subgroup.subgroupOf_eq_top.mpr hLle)
  have hNodd : Odd N.index :=
    hindex.of_dvd_nat (Subgroup.index_dvd_of_le (le_sup_left : L ≤ N))
  have hNmodel : fusionIsBenderGroup (N ⧸ R.subgroupOf N) :=
    rankOneModel_of_equiv (QuotientGroup.quotientInfEquivProdNormalQuotient L R).symm
      hmodel
  exact ⟨⟨N, inferInstance, hstrict, hNodd, hNmodel⟩,
    rank_two_strongEmbedding_conjugate hrank⟩

theorem rank_two_strongEmbedding_explicit_r1Full
    (hrank : TwoRankAtLeastTwo G)
    (H : Subgroup G) (hH : fusionStronglyEmbedded H) :
    (∃ (N : Subgroup G) (_ : N.Normal), oddCore G < N ∧ Odd N.index ∧
      ExplicitRankOneModel (N ⧸ (oddCore G).subgroupOf N)) ∧
      ∀ H₁ H₂ : Subgroup G, fusionStronglyEmbedded H₁ → fusionStronglyEmbedded H₂ →
        ∃ g : G, H₁.map (MulAut.conj g⁻¹).toMonoidHom = H₂ :=
  r1Full_iff_explicit.mp (rank_two_strongEmbedding_r1Full hrank H hH)

end CFSG.ShultStronglyClosedTI
