module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Split
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcBorelQuotientMin
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
public import CFSG.LieType.Chevalley.RootOps.All

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.LieType.Simplicity

section CertificatesF4E8


private theorem permWitness_f4 {K G : Type} [Field K] [Finite K] [Group G] [Finite G]
    (e : G ≃* AdjointQuotient .F4 K) (hK2 : Nat.card K = 2) : PermWitness G := by
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK2, pow_one])
  have : IsSimpleGroup (AdjointQuotient .F4 K) := isSimpleGroup_adjointQuotient_f4 K
  have : IsSimpleGroup G := e.isSimpleGroup
  have : Finite ↥(adjointGroup .F4 K) := generated_group_finite .F4 K
  have h6 : ∀ j, Nat.card (rankOne (f4Datum K).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (f4Datum K).rootGroup j, ∃ b ∈ rankOne (f4Datum K).rootGroup j,
        a * b ≠ b * a := fun j => by
    obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
      (exists_sl2_hom (rootOperatorFamily .F4) (neighbour_F4 j).choose_spec.1)
    exact rankOne_six_of_sl2 hK2 (f4_isParametrization K) hφ hx hy
  have hM : Nat.card K - 1 ∣ 3 := by rw [hK2]; norm_num
  have h := borelQuotient_f4 (K := K) e
  refine permWitness_of_borelQuotient_split h hM ?_ ?_ h6 ?_ ?_
  · have h0 : 0 < (f4Datum K).rank := by show 0 < Tag.rank .F4; decide
    exact diagram_connected_of_card_six h (h6 ⟨0, h0⟩)
  · show 3 ≤ Tag.rank .F4
    decide
  · exact fun j => (hasSL2Node_f4 j).hasOrderThree
  · exact fun j => (hasSL2Node_f4 j).hasOrderThreeNC

private theorem permWitness_e8 {K G : Type} [Field K] [Finite K] [Group G] [Finite G]
    (e : G ≃* AdjointQuotient .E8 K) (hK2 : Nat.card K = 2) : PermWitness G := by
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK2, pow_one])
  have : IsSimpleGroup (AdjointQuotient .E8 K) := isSimpleGroup_adjointQuotient_e8 K
  have : IsSimpleGroup G := e.isSimpleGroup
  have : Finite ↥(adjointGroup .E8 K) := generated_group_finite .E8 K
  have h6 : ∀ j, Nat.card (rankOne (e8Datum K).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (e8Datum K).rootGroup j, ∃ b ∈ rankOne (e8Datum K).rootGroup j,
        a * b ≠ b * a := fun j => by
    obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom_xPar (K := K)
      (exists_sl2_hom (rootOperatorFamily .E8) (neighbour_E8 j).choose_spec.1)
    exact rankOne_six_of_sl2 hK2 (e8_isParametrization K) hφ hx hy
  have hM : Nat.card K - 1 ∣ 3 := by rw [hK2]; norm_num
  have h := borelQuotient_e8 (K := K) e
  refine permWitness_of_borelQuotient_split h hM ?_ ?_ h6 ?_ ?_
  · have h0 : 0 < (e8Datum K).rank := by show 0 < Tag.rank .E8; decide
    exact diagram_connected_of_card_six h (h6 ⟨0, h0⟩)
  · show 3 ≤ Tag.rank .E8
    decide
  · exact fun j => (hasSL2Node_e8 j).hasOrderThree
  · exact fun j => (hasSL2Node_e8 j).hasOrderThreeNC
end CertificatesF4E8

section CertificatesE6


private theorem permWitness_e6 {K G : Type} [Field K] [Finite K] [Group G] [Finite G]
    (e : G ≃* AdjointQuotient .E6 K) (hK2 : Nat.card K = 2) : PermWitness G := by
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK2, pow_one])
  have : IsSimpleGroup (AdjointQuotient .E6 K) := (isQuasisimple_adjointGroup_e6 K).2.1
  have : IsSimpleGroup G := e.isSimpleGroup
  have : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid K
  have h6 : ∀ j, Nat.card (rankOne (e6Datum K).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (e6Datum K).rootGroup j, ∃ b ∈ rankOne (e6Datum K).rootGroup j,
        a * b ≠ b * a := fun j => by
    obtain ⟨φ, hφ, hx, hy⟩ := e6Data_valid.exists_sl2Hom K j
    exact rankOne_six_of_sl2 hK2
      (e6Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E6)) hφ hx hy
  have hM : Nat.card K - 1 ∣ 3 := by rw [hK2]; norm_num
  have h := borelQuotient_e6 (K := K) e
  refine permWitness_of_borelQuotient_split h hM ?_ ?_ h6 ?_ ?_
  · have h0 : 0 < (e6Datum K).rank := by show 0 < Tag.rank .E6; decide
    exact diagram_connected_of_card_six h (h6 ⟨0, h0⟩)
  · show 3 ≤ Tag.rank .E6
    decide
  · exact fun j => (hasSL2Node_e6 j).hasOrderThree
  · exact fun j => (hasSL2Node_e6 j).hasOrderThreeNC

end CertificatesE6

section CertificatesE7


private theorem permWitness_e7 {K G : Type} [Field K] [Finite K] [Group G] [Finite G]
    (e : G ≃* AdjointQuotient .E7 K) (hK2 : Nat.card K = 2) : PermWitness G := by
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK2, pow_one])
  have : IsSimpleGroup (AdjointQuotient .E7 K) := (isQuasisimple_adjointGroup_e7 K).2.1
  have : IsSimpleGroup G := e.isSimpleGroup
  have : Finite ↥(e7Data_valid.minGroup K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e7Data_valid K
  have h6 : ∀ j, Nat.card (rankOne (e7Datum K).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (e7Datum K).rootGroup j, ∃ b ∈ rankOne (e7Datum K).rootGroup j,
        a * b ≠ b * a := fun j => by
    obtain ⟨φ, hφ, hx, hy⟩ := e7Data_valid.exists_sl2Hom K j
    exact rankOne_six_of_sl2 hK2
      (e7Datum_isParametrization K _ (roots_eq isFiniteType_cartan_E7)) hφ hx hy
  have hM : Nat.card K - 1 ∣ 3 := by rw [hK2]; norm_num
  have h := borelQuotient_e7 (K := K) e
  refine permWitness_of_borelQuotient_split h hM ?_ ?_ h6 ?_ ?_
  · have h0 : 0 < (e7Datum K).rank := by show 0 < Tag.rank .E7; decide
    exact diagram_connected_of_card_six h (h6 ⟨0, h0⟩)
  · show 3 ≤ Tag.rank .E7
    decide
  · exact fun j => (hasSL2Node_e7 j).hasOrderThree
  · exact fun j => (hasSL2Node_e7 j).hasOrderThreeNC

end CertificatesE7

theorem permWitnessExcUntwisted_holds :
    PermWitnessExcUntwisted := by
  intro G _ _ t ht hL
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, K, hfield, hfin, hcard, ⟨e⟩⟩ :=
      LieModel.chevalleyExceptionalModel hL
        (by decide : (.F4 : StatedLieTag) ∈ chevalleyExceptionalTags)
    exact permWitness_f4 e (by simpa using hcard)
  · obtain ⟨-, K, hfield, hfin, hcard, ⟨e⟩⟩ :=
      LieModel.chevalleyExceptionalModel hL
        (by decide : (.E6 : StatedLieTag) ∈ chevalleyExceptionalTags)
    exact permWitness_e6 e (by simpa using hcard)
  · obtain ⟨-, K, hfield, hfin, hcard, ⟨e⟩⟩ :=
      LieModel.chevalleyExceptionalModel hL
        (by decide : (.E7 : StatedLieTag) ∈ chevalleyExceptionalTags)
    exact permWitness_e7 e (by simpa using hcard)
  · obtain ⟨-, K, hfield, hfin, hcard, ⟨e⟩⟩ :=
      LieModel.chevalleyExceptionalModel hL
        (by decide : (.E8 : StatedLieTag) ∈ chevalleyExceptionalTags)
    exact permWitness_e8 e (by simpa using hcard)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
