module

public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item145

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem rank3II_15_1 (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hnat : IsNaturalFamily A LB)
    (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {Y : Subgroup G} (hY : Y ∈ scriptY4 A LB) :
    Y = deltaZero A LB Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYY, hYres, hYdelta, -⟩ := hY
  obtain ⟨hdelta, -, hnorm⟩ := rank3II_14_5 hA hnat hbot hYY.2
  set D := deltaZero A LB Y with hD
  set C' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y with hC'
  have hYeq : Y = D ⊔ C' := hYdelta.trans hdelta
  have hYN : Y ≤ Subgroup.normalizer (D : Set G) := hYdelta.le.trans hnorm
  have hDY : D ≤ Y := deltaZero_le Y
  have hC'N : C' ≤ Subgroup.normalizer (D : Set G) := inf_le_right.trans hYN
  have hN : (D.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDY).mpr hYN
  have hcop : Nat.Coprime 3 (Nat.card C') :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 _)
  have key : ∀ x : Y, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ D.subgroupOf Y := by
    rintro x ⟨k, hk⟩
    have hx : (x : G) ∈ ((D : Set G) * (C' : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left D C' hC'N, ← hYeq]
      exact x.2
    obtain ⟨d, hd, c, hc, hdc⟩ := hx
    have hcY : c ∈ Y := (Subgroup.mem_inf.mp hc).2
    have hdY : d ∈ Y := hDY hd
    let π : Y →* Y ⧸ D.subgroupOf Y := QuotientGroup.mk' (D.subgroupOf Y)
    have hπd : π ⟨d, hdY⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mpr (Subgroup.mem_subgroupOf.mpr hd)
    have hπx : π x = π ⟨c, hcY⟩ := by
      have hxdc : x = ⟨d, hdY⟩ * ⟨c, hcY⟩ := Subtype.ext hdc.symm
      rw [hxdc, map_mul, hπd, one_mul]
    have hc1 : (⟨c, hcY⟩ : Y) ^ Nat.card C' = 1 := by
      have h : (⟨c, hc⟩ : C') ^ Nat.card C' = 1 := pow_card_eq_one'
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h' ⊢
      exact h'
    have h1 : π x ^ Nat.card C' = 1 := by rw [hπx, ← map_pow, hc1, map_one]
    have h2 : π x ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
    have hord : orderOf (π x) = 1 := Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcop).gcd_eq_one ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1))
    rw [orderOf_eq_one_iff] at hord
    exact (QuotientGroup.eq_one_iff (N := D.subgroupOf Y) _).mp hord
  have hres : oPrimeResidualOf 3 Y ≤ D := by
    unfold oPrimeResidualOf oPrimeResidual
    rw [← Subgroup.map_subgroupOf_eq_of_le hDY]
    exact Subgroup.map_mono ((Subgroup.closure_le _).mpr fun x hx => key x hx)
  exact le_antisymm (hYres.le.trans hres) hDY

end CFSG.RankThree.PartTwo.Sec15
