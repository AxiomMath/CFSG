module

public import CFSG.RankThree.GF2n.Parrott.ExtraspecialJ

public section

namespace CFSG.RankThree.GF2n.Parrott.QuotientV

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem centerIn_subgroupOf_eq_center (z : G) :
    (centerIn (J z)).subgroupOf (J z) = Subgroup.center (J z) := by
  rw [centerIn_eq_map_center]
  exact Subgroup.comap_map_eq_self_of_injective (J z).subtype_injective (Subgroup.center (J z))

instance centerIn_subgroupOf_normal (z : G) :
    ((centerIn (J z)).subgroupOf (J z)).Normal := by
  rw [centerIn_subgroupOf_eq_center]
  infer_instance

abbrev V (z : G) : Type :=
  J z ⧸ (centerIn (J z)).subgroupOf (J z)

@[expose] noncomputable def pi (z : G) : J z →* V z :=
  QuotientGroup.mk' ((centerIn (J z)).subgroupOf (J z))

theorem pi_surjective (z : G) : Function.Surjective (pi z) :=
  QuotientGroup.mk'_surjective _

theorem pi_ker (z : G) : (pi z).ker = (centerIn (J z)).subgroupOf (J z) :=
  QuotientGroup.ker_mk' _

theorem card_V (h : Tim79a.ParrottHyp z) : Nat.card (V z) = 2 ^ 8 := by
  have hZsub : Nat.card ((centerIn (J z)).subgroupOf (J z)) = 4 := by
    rw [centerIn_subgroupOf_eq_center, ← card_centerIn_J h, centerIn_eq_map_center,
      Subgroup.card_map_of_injective (J z).subtype_injective]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((centerIn (J z)).subgroupOf (J z))
  rw [card_J h, hZsub] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (hcard.symm.trans (by norm_num))

theorem isMulCommutative_V (h : Tim79a.ParrottHyp z) : IsMulCommutative (V z) := by
  have hJcomm : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  have hz_center : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hzp : Subgroup.zpowers z ≤ centerIn (J z) := Subgroup.zpowers_le_of_mem hz_center
  intro x hx
  apply Subgroup.mem_subgroupOf.mpr
  have hx' : (x : G) ∈ ⁅J z, J z⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  rw [hJcomm] at hx'
  exact hzp hx'

theorem pow_two_eq_one_V (h : Tim79a.ParrottHyp z) (v : V z) : v ^ 2 = 1 := by
  obtain ⟨j, rfl⟩ := pi_surjective z v
  have hj : ((j : J z) : G) * ((j : J z) : G) ∈ centerIn (J z) :=
    sq_mem_centerIn_J h j.2
  have hker : j * j ∈ (pi z).ker := by
    rw [pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hj
  have hmap : pi z (j * j) = 1 := MonoidHom.mem_ker.mp hker
  simpa [pow_two, map_mul] using hmap

end CFSG.RankThree.GF2n.Parrott.QuotientV
