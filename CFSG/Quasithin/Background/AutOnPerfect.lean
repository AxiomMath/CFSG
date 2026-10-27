module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open

variable {G : Type*} [Group G]

theorem autOn_perfect {K V : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hKK : ⁅K, K⁆ = K) : ⁅autOn K V, autOn K V⁆ = autOn K V := by
  set N := Subgroup.normalizer (V : Set G)
  have hK' : ⁅K.subgroupOf N, K.subgroupOf N⁆ = K.subgroupOf N := by
    have h1 : (⁅K.subgroupOf N, K.subgroupOf N⁆).map N.subtype = K := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKV, hKK]
    calc ⁅K.subgroupOf N, K.subgroupOf N⁆ =
          ((⁅K.subgroupOf N, K.subgroupOf N⁆).map N.subtype).subgroupOf N :=
        (Subgroup.comap_map_eq_self_of_injective N.subtype_injective _).symm
      _ = K.subgroupOf N := by rw [h1]
  unfold autOn
  rw [← Subgroup.map_commutator, hK']

theorem autOn_perfectCore_eq [Finite G] {X V : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    autOn (perfectCore X) V = perfectCore (autOn X V) := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : (perfectCore (X.subgroupOf N)).map N.subtype = perfectCore X := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hX]
  have h2 : perfectCore (X.subgroupOf N) = (perfectCore X).subgroupOf N := by
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective _).symm
  unfold autOn
  rw [← h2, map_perfectCore]

end CFSG.Quasithin.AutOn
