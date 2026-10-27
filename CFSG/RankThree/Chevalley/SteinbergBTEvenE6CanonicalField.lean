module

public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley SteinbergBT

theorem even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer {d m : ℕ}
    (hd : 1 ≤ d) (hm : 2 ≤ m) (K : Type) [Field K] (hK : Nat.card K = 2 ^ (d * m))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ d) :
    (∀ c : K, c ∈ fixSubfield σ ↔ c ^ 2 ^ d = c) ∧
      orderOf (entrywiseAdjointAut TwistTag.E6.tag σ) = m ∧
      ⁅MonoidHom.eqLocus (entrywiseAdjointAut TwistTag.E6.tag σ).toMonoidHom
          (MonoidHom.id (adjointGroup TwistTag.E6.tag K)),
        MonoidHom.eqLocus (entrywiseAdjointAut TwistTag.E6.tag σ).toMonoidHom
          (MonoidHom.id (adjointGroup TwistTag.E6.tag K))⁆ =
        (fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K) ∧
      fixedFieldImage TwistTag.E6.tag σ ≤ adjointGroup TwistTag.E6.tag K ∧
      IsSimpleGroup (fixedFieldImage TwistTag.E6.tag σ) ∧
      (¬∀ a b : fixedFieldImage TwistTag.E6.tag σ, a * b = b * a) ∧
      (∃ ι : ↥((fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K)) ≃*
          ↥(((fixedFieldImage TwistTag.E6.tag σ).subgroupOf
            (adjointGroup TwistTag.E6.tag K)).map MulAut.conj),
        ∀ j, (ι j : MulAut (adjointGroup TwistTag.E6.tag K)) =
          MulAut.conj (j : adjointGroup TwistTag.E6.tag K)) ∧
      ((fixedFieldImage TwistTag.E6.tag σ).subgroupOf (adjointGroup TwistTag.E6.tag K)).map
          MulAut.conj ≤ Subgroup.centralizer {entrywiseAdjointAut TwistTag.E6.tag σ} ∧
      ((((fixedFieldImage TwistTag.E6.tag σ).subgroupOf
          (adjointGroup TwistTag.E6.tag K)).map MulAut.conj).subgroupOf
        (Subgroup.centralizer {entrywiseAdjointAut TwistTag.E6.tag σ})).Normal ∧
      Subgroup.centralizer {entrywiseAdjointAut TwistTag.E6.tag σ} ⊓
          Subgroup.centralizer ((((fixedFieldImage TwistTag.E6.tag σ).subgroupOf
            (adjointGroup TwistTag.E6.tag K)).map MulAut.conj :
              Subgroup (MulAut (adjointGroup TwistTag.E6.tag K))) :
                Set (MulAut (adjointGroup TwistTag.E6.tag K))) =
        Subgroup.zpowers (entrywiseAdjointAut TwistTag.E6.tag σ) ∧
      Nat.card (Subgroup.zpowers (entrywiseAdjointAut TwistTag.E6.tag σ)) = m := by
  have hdm : 1 ≤ d * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  set C := adjointGroup TwistTag.E6.tag K
  set δ := entrywiseAdjointAut TwistTag.E6.tag σ with hδ
  set J := fixedFieldImage TwistTag.E6.tag σ with hJ
  have hrank : 0 < TwistTag.E6.tag.rank := by decide
  have hZ : Subgroup.center C = ⊥ := center_adjointGroup_eq_bot_field _ K
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hdm hK
  have hσfr : σ = fr ^ d := RingEquiv.ext fun c => by
    rw [hσ, ringAut_pow_apply_of_frobenius hfr d c]
  have hσord : orderOf σ = m := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro m rfl), hord,
      Nat.mul_div_cancel_left m (by omega)]
  have hδord : orderOf δ = m := by rw [orderOf_entrywiseAdjointAut hrank σ, hσord]
  have hFδ : MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C) =
      (entrywiseFixedGroup TwistTag.E6.tag σ).subgroupOf C := by
    ext g
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have hder : ⁅MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C),
      MonoidHom.eqLocus δ.toMonoidHom (MonoidHom.id C)⁆ = J.subgroupOf C := by
    rw [hFδ, commutator_subgroupOf_eq (H := entrywiseFixedGroup TwistTag.E6.tag σ) inf_le_left,
      commutator_entrywiseFixedGroup_eq (τ := TwistTag.E6.tag) (Or.inr (Or.inr (Or.inl rfl)))]
  have hJC : J ≤ C := fun j hj => (fixedFieldImage_le hj).1
  set k := fixSubfield σ
  have hsimple : IsSimpleGroup J := by
    have hq := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k
    have hZk : Subgroup.center (adjointGroup Tag.E6 k) = ⊥ := center_adjointGroup_eq_bot_field _ k
    exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
      ((Subgroup.equivMapOfInjective (adjointGroup Tag.E6 k) _
        (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot).symm)
  obtain ⟨hinjOn, hle, hnormal⟩ := derivedFixed_inner_normal hZ hder
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have hcent := FieldGraphFieldPointwise.centralizer_inf_eq_zpowers_of_fix hZ hle
    fun β hβ => FieldGraphFieldPointwise.mem_zpowers_of_forall_fixedFieldImage σ hβ
  exact ⟨fun c => by rw [mem_fixSubfield, hσ], hδord, hder, hJC, hsimple,
    not_commute_fixedFieldImage hrank σ,
    ⟨(J.subgroupOf C).equivMapOfInjective _ hinj, fun j => rfl⟩, hle, hnormal, hcent,
    by rw [Nat.card_zpowers, hδord]⟩

end CFSG.RankThree.Chevalley
