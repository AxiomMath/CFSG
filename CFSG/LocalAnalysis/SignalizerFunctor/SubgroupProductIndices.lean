module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem subgroup_card_mul_relIndex (subgroup parent : Subgroup GroupType) (contained : subgroup ≤ parent) :
    Nat.card subgroup * subgroup.relIndex parent = Nat.card parent := by
  have formula := (subgroup.subgroupOf parent).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe contained).toEquiv] at formula
  exact formula

theorem subgroup_inf_relIndex (first second : Subgroup GroupType) :
    (first ⊓ second).relIndex second = first.relIndex second := by
  simpa only [inf_idem, Subgroup.relIndex_self, mul_one] using
    (Subgroup.relIndex_inf_mul_relIndex first second second).symm

variable [Finite GroupType]

theorem subgroup_product_relIndex (parent first second : Subgroup GroupType)
    (first_le : first ≤ parent) (second_le : second ≤ parent)
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    second.relIndex parent = second.relIndex first := by
  have formula := subgroup_product_cardinality_of_subgroup_whole parent first second first_le second_le
    ((subgroup_product_eq_subgroup_iff parent first second first_le second_le).mp whole)
  have parent_index := subgroup_card_mul_relIndex second parent second_le
  have first_index := subgroup_card_mul_relIndex (second ⊓ first) first inf_le_right
  rw [subgroup_inf_relIndex, inf_comm second first] at first_index
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := (first ⊓ second : Subgroup GroupType)))
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := second))
  calc
    Nat.card second * (second.relIndex parent * Nat.card (first ⊓ second : Subgroup GroupType)) =
        Nat.card parent * Nat.card (first ⊓ second : Subgroup GroupType) := by rw [← mul_assoc, parent_index]
    _ = Nat.card first * Nat.card second := formula.symm
    _ = Nat.card second * (second.relIndex first * Nat.card (first ⊓ second : Subgroup GroupType)) := by
      rw [mul_comm (second.relIndex first), first_index, mul_comm]

theorem normalizing_subgroup_relIndex_dvd (parent normal subgroup : Subgroup GroupType)
    (normal_le : normal ≤ parent) (subgroup_le : subgroup ≤ parent)
    (normalized : subgroup ≤ Subgroup.normalizer (normal : Set GroupType)) :
    subgroup.relIndex normal ∣ subgroup.relIndex parent := by
  have join_le : normal ⊔ subgroup ≤ parent := sup_le normal_le subgroup_le
  have product : subgroupProduct normal subgroup = ((normal ⊔ subgroup : Subgroup GroupType) : Set GroupType) := by
    apply (subgroup_product_eq_subgroup_iff _ normal subgroup le_sup_left le_sup_right).mpr
    intro element member
    exact (mem_sup_of_normalizing normal subgroup normalized element).mp member
  have index_equal := subgroup_product_relIndex (normal ⊔ subgroup) normal subgroup le_sup_left le_sup_right product
  have formula := Subgroup.relIndex_mul_relIndex subgroup (normal ⊔ subgroup) parent le_sup_right join_le
  exact ⟨(normal ⊔ subgroup).relIndex parent, by rw [index_equal] at formula; exact formula.symm⟩

theorem sylow_containment_relIndex_coprime (prime : ℕ) (prime_prime : prime.Prime)
    (parent subgroup : Subgroup GroupType) (sylow : Sylow prime parent)
    (contained : (sylow : Subgroup parent).map parent.subtype ≤ subgroup) :
    Nat.Coprime prime (subgroup.relIndex parent) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have internal_contained : (sylow : Subgroup parent) ≤ subgroup.subgroupOf parent := by
    intro element member
    exact contained (Subgroup.mem_map_of_mem parent.subtype member)
  have divides := Subgroup.relIndex_dvd_of_le_left (⊤ : Subgroup parent) internal_contained
  simp only [Subgroup.relIndex_top_right] at divides
  exact prime_prime.coprime_iff_not_dvd.mpr (fun prime_divides => sylow.not_dvd_index (prime_divides.trans divides))

theorem sylow_exists_le_of_relIndex_coprime (prime : ℕ) (prime_prime : prime.Prime)
    (parent subgroup : Subgroup GroupType) (coprime : Nat.Coprime prime (subgroup.relIndex parent)) :
    ∃ sylow : Sylow prime parent, (sylow : Subgroup parent).map parent.subtype ≤ subgroup := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let internalSylow : Sylow prime (subgroup.subgroupOf parent) := Classical.choice inferInstance
  obtain ⟨sylow, equal⟩ := sylow_lift_of_coprime_index prime prime_prime (subgroup.subgroupOf parent) coprime internalSylow
  refine ⟨sylow, ?_⟩
  rw [equal]
  intro element member
  obtain ⟨representative, representative_member, rfl⟩ := member
  obtain ⟨internal, _, image⟩ := representative_member
  rw [← image]
  exact internal.property

end CFSG.SignalizerFunctor.Helpers
