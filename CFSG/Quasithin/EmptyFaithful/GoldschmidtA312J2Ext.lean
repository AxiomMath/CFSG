module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Frat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Perf
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.A312J2

open CFSG.Quasithin

theorem isExt_of_perfect_card_1920 {Y : Type} [Group Y] [Finite Y] (hY : Nat.card Y = 1920)
    (hperf : Group.IsPerfect Y) (Q : Subgroup Y) [Q.Normal] (hQ : Nat.card Q = 32)
    (hC : Nat.card (Subgroup.centralizer (Q : Set Y)) = 2) :
    IsExt Y (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 5 (by rw [hY]; norm_num)
  have hext := isExtraspecial_of_card_thirtyTwo Q hQ hC hx
  have hq : Nat.card (Y ⧸ Q) = 60 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    rw [hY, hQ] at h
    omega
  have hperfq : Group.IsPerfect (Y ⧸ Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective Q)
  exact ⟨Q, inferInstance, ⟨hext, by rw [hQ]; norm_num⟩,
    nonempty_mulEquiv_alt5_of_perfect hperfq hq⟩

theorem map_centralizer_subgroupOf {G : Type} [Group G] {C Q : Subgroup G} (hQC : Q ≤ C) :
    (Subgroup.centralizer (Q.subgroupOf C : Set ↥C)).map C.subtype =
      C ⊓ Subgroup.centralizer (Q : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun q hq => ?_⟩
    have := hz ⟨q, hQC hq⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hq)
    exact congrArg Subtype.val this
  · rintro ⟨hyC, hy⟩
    refine ⟨⟨y, hyC⟩, fun h hh => ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hh
    exact Subtype.ext (hy (h : G) hh)

theorem isExt_of_subgroup_data {G : Type} [Group G] {C Q : Subgroup G} (hC : Nat.card C = 1920)
    (hperf : ⁅C, C⁆ = C) (hQC : Q ≤ C) (hCQ : C ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Nat.card Q = 32) (hcent : Nat.card ↥(C ⊓ Subgroup.centralizer (Q : Set G)) = 2) :
    IsExt ↥C (fun V _ => IsExtraspecial2 2 V) (fun Z _ => IsAlt 5 Z) := by
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hn : (Q.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQC).mpr hCQ
  refine isExt_of_perfect_card_1920 hC (Subgroup.isPerfect_iff.mpr hperf) (Q.subgroupOf C) ?_ ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQ]
  · rw [← Subgroup.card_map_of_injective C.subtype_injective, map_centralizer_subgroupOf hQC,
      hcent]

end CFSG.Quasithin.A312J2
