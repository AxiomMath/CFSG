module

public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.GoldschmidtTDE68Thr

public section

namespace CFSG.Quasithin.E6.Qs

open Subgroup

theorem sixty_le_index_center {K : Type*} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) :
    60 ≤ (Subgroup.center K).index := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  exact CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty hs ⟨a, b, hab⟩

theorem false_of_hom_solvable {K G : Type*} [Group K] [Finite K] [Group G]
    (hq : CFSG.IsQuasisimple K) (κ : K →* G) (hker : κ.ker ≤ Subgroup.center K)
    (hsolv : Group.IsSolvable ↥κ.range) : False := by
  have hcen : Group.IsSolvable ↥(Subgroup.center K) := inferInstance
  have hkerS : Group.IsSolvable ↥κ.ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hker)
      (Subgroup.inclusion_injective hker)
  have hKS : Group.IsSolvable K := by
    refine Group.isSolvable_of_ker_le_range κ.ker.subtype κ.rangeRestrict ?_
    rw [Subgroup.range_subtype, MonoidHom.ker_rangeRestrict]
  have hnt : Nontrivial K := by
    have : Nontrivial (K ⧸ Subgroup.center K) := hq.2.1.toNontrivial
    exact (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  have := hq.1
  exact Group.IsPerfect.not_isSolvable K hKS

theorem card_eq_sixty_of_hom {K G : Type*} [Group K] [Finite K] [Group G]
    (hq : CFSG.IsQuasisimple K) (κ : K →* G) (hker : κ.ker ≤ Subgroup.center K)
    (hker3 : Nat.card κ.ker ∣ 3) (N : Subgroup G) (hN : Nat.card N = 60)
    (hrange : κ.range ≤ N) : Nat.card K = 60 := by
  have hNfin : Finite N := Nat.finite_of_card_ne_zero (by rw [hN]; norm_num)
  have h1 : κ.ker.index = Nat.card κ.range := Subgroup.index_ker κ
  have h2 : Nat.card κ.range ≤ 60 := hN ▸ Subgroup.card_le_of_le hrange
  have h3 : (Subgroup.center K).index ∣ κ.ker.index := Subgroup.index_dvd_of_le hker
  have hpos : 0 < κ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h4 : 60 ≤ κ.ker.index :=
    (sixty_le_index_center hq).trans (Nat.le_of_dvd hpos h3)
  have h5 : κ.ker.index = 60 := by omega
  have hmul := Subgroup.index_mul_card κ.ker
  rw [h5] at hmul
  have hcard : Nat.card κ.ker = 1 ∨ Nat.card κ.ker = 3 := by
    have : Nat.card κ.ker ∈ Nat.divisors 3 := Nat.mem_divisors.2 ⟨hker3, by norm_num⟩
    have h13 : Nat.divisors 3 = {1, 3} := by decide
    rw [h13] at this
    simpa using this
  rcases hcard with h | h
  · rw [h] at hmul
    omega
  · exfalso
    have hnt : Nontrivial κ.ker := Finite.one_lt_card_iff_nontrivial.1 (by rw [h]; norm_num)
    obtain ⟨z, hz⟩ := exists_ne (1 : κ.ker)
    have hz3 : (z : K) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := κ.ker) (x := z)
      rw [h] at this
      exact congrArg Subtype.val this
    have hK : Nat.card K ∣ 180 := by
      rw [h] at hmul
      exact ⟨1, by omega⟩
    have := hq.1
    have hz1 : (z : K) = 1 :=
      Thr.eq_one_of_central_three hq.1 hK z (hker z.2) hz3
    exact hz (Subtype.ext hz1)

end CFSG.Quasithin.E6.Qs
