module

public import CFSG.LocalAnalysis.SignalizerFunctor.Coprime
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.CocycleAveraging

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] noncomputable def complementQuotientEquiv (normal complement : Subgroup GroupType)
    [normal.Normal] (complementary : normal.IsComplement' complement) :
    complement ≃* GroupType ⧸ normal := by
  let projection := QuotientGroup.mk' normal
  let restricted := projection.comp complement.subtype
  have injective : Function.Injective restricted := by
    apply (injective_iff_map_eq_one restricted).mpr
    intro element trivial
    have normal_member : element.val ∈ normal := (QuotientGroup.eq_one_iff _).mp trivial
    have intersection_member : element.val ∈ normal ⊓ complement :=
      ⟨normal_member, element.property⟩
    rw [complementary.disjoint.eq_bot] at intersection_member
    exact Subtype.ext intersection_member
  have surjective : Function.Surjective restricted := by
    intro element
    obtain ⟨representative, rfl⟩ := QuotientGroup.mk'_surjective normal element
    have member : representative ∈ normal ⊔ complement := by
      rw [complementary.sup_eq_top]
      trivial
    obtain ⟨normalElement, normal_member, complementElement, complement_member, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp member
    refine ⟨⟨complementElement, complement_member⟩, ?_⟩
    change projection complementElement = projection (normalElement * complementElement)
    have normal_trivial : projection normalElement = 1 :=
      (QuotientGroup.eq_one_iff _).mpr normal_member
    rw [map_mul, normal_trivial, one_mul]
  exact MulEquiv.ofBijective restricted ⟨injective, surjective⟩

theorem complement_quotient_equiv_apply (normal complement : Subgroup GroupType)
    [normal.Normal] (complementary : normal.IsComplement' complement) (element : complement) :
    complementQuotientEquiv normal complement complementary element =
      QuotientGroup.mk' normal element.val := rfl

theorem abelian_normal_complements_conjugate [Finite GroupType]
    (normal first second : Subgroup GroupType) [normal.Normal]
    (commutative : IsMulCommutative normal)
    (coprime : Nat.Coprime (Nat.card normal) normal.index)
    (first_complementary : normal.IsComplement' first)
    (second_complementary : normal.IsComplement' second) :
    ∃ element : normal, conjugateSubgroup element.val first = second := by
  let := commutative
  let _normalCommGroup : CommGroup normal := { normal.toGroup with mul_comm := mul_comm' }
  let _action := conjugationAction first normal Subgroup.le_normalizer_of_normal
  let projection := QuotientGroup.mk' normal
  let firstProjection := complementQuotientEquiv normal first first_complementary
  let secondProjection := complementQuotientEquiv normal second second_complementary
  let lift : first ≃* second := firstProjection.trans secondProjection.symm
  have projection_equal : ∀ element : first, projection (lift element).val =
      projection element.val := by
    intro element
    change secondProjection (secondProjection.symm (firstProjection element)) =
      firstProjection element
    exact secondProjection.apply_symm_apply _
  let cocycle : first → normal := fun element =>
    ⟨(lift element).val * element.val⁻¹, by
      apply (QuotientGroup.eq_one_iff _).mp
      change projection ((lift element).val * element.val⁻¹) = 1
      rw [map_mul, map_inv, projection_equal, mul_inv_cancel]⟩
  have cocycle_law : ∀ firstElement secondElement : first,
      cocycle (firstElement * secondElement) = cocycle firstElement *
        (firstElement • cocycle secondElement) := by
    intro firstElement secondElement
    apply Subtype.ext
    have lift_mul := congrArg (fun internal : second => (internal : GroupType))
      (map_mul lift firstElement secondElement)
    change (lift (firstElement * secondElement)).val =
      (lift firstElement).val * (lift secondElement).val at lift_mul
    change (lift (firstElement * secondElement)).val *
      (firstElement.val * secondElement.val)⁻¹ =
      ((lift firstElement).val * firstElement.val⁻¹) *
        (firstElement.val * ((lift secondElement).val * secondElement.val⁻¹) *
          firstElement.val⁻¹)
    rw [lift_mul]
    group
  have first_coprime : Nat.Coprime (Nat.card normal) (Nat.card first) := by
    rw [← first_complementary.symm.index_eq_card]
    exact coprime
  obtain ⟨average, principal⟩ := coprime_multiplicative_cocycle_principal first normal
    first_coprime cocycle cocycle_law
  have conjugates_element : ∀ element : first,
      average.val * element.val * average.val⁻¹ = (lift element).val := by
    intro element
    have equality := congrArg (fun internal : normal => (internal : GroupType))
      (principal element)
    change (lift element).val * element.val⁻¹ =
      average.val * (element.val * average.val * element.val⁻¹)⁻¹ at equality
    calc
      average.val * element.val * average.val⁻¹ =
          (average.val * (element.val * average.val * element.val⁻¹)⁻¹) * element.val := by
        group
      _ = ((lift element).val * element.val⁻¹) * element.val := by rw [← equality]
      _ = (lift element).val := by group
  refine ⟨average, ?_⟩
  apply le_antisymm
  · rintro element ⟨representative, member, rfl⟩
    change average.val * representative * average.val⁻¹ ∈ second
    rw [conjugates_element (⟨representative, member⟩ : first)]
    exact (lift (⟨representative, member⟩ : first)).property
  · intro element member
    refine ⟨(lift.symm (⟨element, member⟩ : second)).val,
      (lift.symm (⟨element, member⟩ : second)).property, ?_⟩
    change average.val * (lift.symm (⟨element, member⟩ : second)).val * average.val⁻¹ = element
    rw [conjugates_element]
    exact congrArg (fun internal : second => (internal : GroupType)) (lift.apply_symm_apply _)

end CFSG.SignalizerFunctor.Helpers
