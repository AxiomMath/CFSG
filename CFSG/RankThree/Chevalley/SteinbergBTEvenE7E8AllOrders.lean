module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT

theorem even_E7_E8_canonical_field_centralizer_all_orders (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) :
    ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (adjointGroup τ K).subtype = fixedFieldImage τ σ ∧
      fixedFieldImage τ σ ≤ adjointGroup τ K ∧
      IsSimpleGroup (fixedFieldImage τ σ) ∧ (¬∀ a b : fixedFieldImage τ σ, a * b = b * a) ∧
      (∃ ι : ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) ≃*
          ↥(((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup τ K)) = MulAut.conj (j : adjointGroup τ K)) ∧
      (∀ β ∈ Subgroup.centralizer {entrywiseAdjointAut τ σ},
        ∃! gφ : adjointGroup τ K × (K ≃+* K), (gφ.1 : ModGL τ K) ∈ fixedFieldImage τ σ ∧
          ∀ h : adjointGroup τ K, (β h : ModGL τ K) = (gφ.1 : ModGL τ K) *
            Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) *
              (gφ.1 : ModGL τ K)⁻¹) ∧
      (∀ g : adjointGroup τ K, (g : ModGL τ K) ∈ fixedFieldImage τ σ → ∀ φ : K ≃+* K,
        MulAut.conj g * entrywiseAdjointAut τ φ ∈
          Subgroup.centralizer {entrywiseAdjointAut τ σ}) ∧
      ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj ≤
        Subgroup.centralizer {entrywiseAdjointAut τ σ} ∧
      ((((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut τ σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut τ σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage τ σ).subgroupOf
            (adjointGroup τ K)).map MulAut.conj : Subgroup (MulAut (adjointGroup τ K))) :
              Set (MulAut (adjointGroup τ K))) =
        Subgroup.zpowers (entrywiseAdjointAut τ σ) ∧
      Nat.card (Subgroup.zpowers (entrywiseAdjointAut τ σ)) = orderOf σ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hf hK
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hΓJ := entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
    (Or.inr (Or.inr (Or.inr hτ))) hchar σ
  have hNF := (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ).1
  obtain ⟨hdvd, hk⟩ := card_fixSubfield Nat.prime_two hf hK σ
  have hd : 1 ≤ f / orderOf σ :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_dvd_of_pos hdvd (by omega))
  have hNFk := (even_E7_E8_exact_inner_field_automorphism_normal_form hd (fixSubfield σ) hk τ
    hτ).1
  obtain ⟨hJC, hfixJ, hι, huniq, hactor, hNδ, hnormal, hcent⟩ :=
    canonical_field_centralizer_of_normalForm_all σ hNF hNFk hΓJ
  have hZk : Subgroup.center (adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  set eJ : fixedFieldImage τ σ ≃* AdjointQuotient τ (fixSubfield σ) :=
    (fixedFieldImageEquiv σ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm
  have hsimple : IsSimpleGroup (fixedFieldImage τ σ) := by
    rcases hτ with rfl | rfl
    · exact (CFSG.LieType.Simplicity.fam_e7_simplicity _ 2 (f / orderOf σ)
        ⟨⟨Nat.prime_two, hd, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk, ⟨eJ⟩⟩).2
    · exact (CFSG.LieType.Simplicity.fam_e8_simplicity _ 2 (f / orderOf σ)
        ⟨⟨Nat.prime_two, hd, rfl⟩, fixSubfield σ, inferInstance, inferInstance, hk, ⟨eJ⟩⟩).2
  have hrank : 0 < τ.rank := by
    rcases hτ with rfl | rfl <;> decide
  exact ⟨hfixJ, hJC, hsimple, not_commute_fixedFieldImage hrank σ, hι, huniq, hactor, hNδ,
    hnormal, hcent, by rw [Nat.card_zpowers, orderOf_entrywiseAdjointAut hrank σ]⟩

end CFSG.RankThree.Chevalley
