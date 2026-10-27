module

public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem normalizer_le_centralizer_of_characteristic {U : Subgroup G} {t : G} (ht : orderOf t = 2)
    (htU : t ∈ U) (hchar : ((zpowers t).subgroupOf U).Characteristic) :
    normalizer (U : Set G) ≤ centralizer ({t} : Set G) := by
  intro x hx
  set φ := U.normalizerMonoidHom ⟨x, hx⟩
  have hmem : φ ⟨t, htU⟩ ∈ (zpowers t).subgroupOf U := by
    rw [← (characteristic_iff_map_eq.mp hchar φ)]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr (mem_zpowers t))
  have hconj : x * t * x⁻¹ ∈ zpowers t := by
    have := mem_subgroupOf.mp hmem
    rwa [normalizerMonoidHom_apply_apply_coe] at this
  rw [mem_centralizer_singleton_iff]
  rcases (mem_zpowers_iff_of_orderOf_eq_two ht).mp hconj with h | h
  · have ht1 : t = 1 := by
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [h]

theorem isSylowOf_of_isSylowOf_inf_centralizer [Finite G] {H U : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htU : t ∈ U) (hchar : ((zpowers t).subgroupOf U).Characteristic)
    (hU : IsSylowOf 2 U (H ⊓ centralizer ({t} : Set G))) : IsSylowOf 2 U H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_normalizer_inf_le (by rwa [inf_comm])
    (inf_le_left.trans (normalizer_le_centralizer_of_characteristic ht htU hchar))

end CFSG.OddTranspositions.PartThree.Wong
