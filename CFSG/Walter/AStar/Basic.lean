module

public import CFSG.Walter.Defs
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Walter

variable {G : Type*} [Group G]

theorem hasAbelianSylowTwo_of_sylow [Finite G] (P : Sylow 2 G)
    (hP : IsMulCommutative (P : Subgroup G)) : HasAbelianSylowTwo G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact Subgroup.map_isMulCommutative _ _

theorem HasAbelianSylowTwo.subgroup [Finite G] (hG : HasAbelianSylowTwo G) (H : Subgroup G) :
    HasAbelianSylowTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map H.subtype).exists_le_sylow
  have := hG Q
  have : IsMulCommutative ((P : Subgroup H).map H.subtype) := isMulCommutative_anti hQ
  have h := Subgroup.comap_injective_isMulCommutative (H := (P : Subgroup H).map H.subtype)
    H.subtype_injective
  rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at h

theorem HasAbelianSylowTwo.of_surjective [Finite G] {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) (hG : HasAbelianSylowTwo G) : HasAbelianSylowTwo G' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G' := Finite.of_surjective f hf
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  refine hasAbelianSylowTwo_of_sylow (P.mapSurjective hf) ?_
  rw [Sylow.coe_mapSurjective]
  have := hG P
  exact Subgroup.map_isMulCommutative _ _

theorem HasAbelianSylowTwo.quotient [Finite G] (hG : HasAbelianSylowTwo G) (N : Subgroup G)
    [N.Normal] : HasAbelianSylowTwo (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk'_surjective N)

theorem even_card_of_isSimpleGroup [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Even (Nat.card G) := by
  by_contra hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

end CFSG.Walter
