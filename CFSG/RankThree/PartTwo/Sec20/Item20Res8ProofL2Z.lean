module

import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

namespace Res8

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_centralizer_of_comm_mem {Y O : Subgroup G} {c y : G} (hcY : c ∈ Y)
    (hc : orderOf c = 3) (hO : Nat.Coprime 3 (Nat.card O))
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hy : y ∈ Y) (hyc : y * c * y⁻¹ * c⁻¹ ∈ O) :
    ∃ u ∈ O ⊓ Y, ∃ y' ∈ Y ⊓ Subgroup.centralizer ({c} : Set G), y = u * y' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₀ := O ⊓ Y with hN₀
  set C3 := Subgroup.zpowers c with hC3
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hYN₀ : Y ≤ Subgroup.normalizer (N₀ : Set G) := fun g hg =>
    Sec20.mem_normalizer_inf_of_mem (hYO hg) (Subgroup.le_normalizer hg)
  have hC3Y : C3 ≤ Y := Subgroup.zpowers_le.mpr hcY
  have hN₀Y : N₀ ≤ Y := inf_le_right
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO
      (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 C3 (C3 ⊔ N₀) :=
    Sec20.isSylowOf_sup_of_coprime (Sec20.isPGroup_zpowers_of_pow_three hc3) hN₀3
      (hC3Y.trans hYN₀)
  have hycN : y * c * y⁻¹ * c⁻¹ ∈ N₀ :=
    ⟨hyc, Y.mul_mem (Y.mul_mem (Y.mul_mem hy hcY) (Y.inv_mem hy)) (Y.inv_mem hcY)⟩
  have hyN : y ∈ Subgroup.normalizer ((C3 ⊔ N₀ : Subgroup G) : Set G) := by
    apply Sec20.mem_normalizer_of_map_conj_le
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.zpowers_le, Subgroup.mem_comap]
      change y * c * y⁻¹ ∈ C3 ⊔ N₀
      have : y * c * y⁻¹ = (y * c * y⁻¹ * c⁻¹) * c := by group
      rw [this]
      exact (C3 ⊔ N₀).mul_mem (Subgroup.mem_sup_right hycN)
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    · refine le_trans ?_ le_sup_right
      rintro _ ⟨o, ho, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hYN₀ hy) o).mp ho
  obtain ⟨n, hn, w, hw, rfl⟩ := Sec18.exists_mul_of_isSylowOf hsyl
    (Subgroup.zpowers_le.mpr hyN) (Subgroup.mem_zpowers y)
  have hn' : n ∈ ((C3 ⊔ N₀ : Subgroup G) : Set G) := hn
  rw [Subgroup.coe_mul_of_left_le_normalizer_right C3 N₀ (hC3Y.trans hYN₀)] at hn'
  obtain ⟨d, hd, u, hu, rfl⟩ := hn'
  have hdY : d ∈ Y := hC3Y hd
  have huY : u ∈ Y := hN₀Y hu
  have hwY : w ∈ Y := by
    have e : w = (d * u)⁻¹ * (d * u * w) := by group
    rw [e]
    exact Y.mul_mem (Y.inv_mem (Y.mul_mem hdY huY)) hy
  have hdc : d ∈ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.zpow_self c k).eq
  have hwc : w ∈ Subgroup.centralizer ({c} : Set G) := by
    have h1 : w * c * w⁻¹ * c⁻¹ ∈ O := by
      have hdO : ∀ o ∈ O, d * o * d⁻¹ ∈ O := fun o ho =>
        (Subgroup.mem_normalizer_iff.mp (hYO hdY) o).mp ho
      have huO : u ∈ O := hu.1
      have hcO : ∀ o ∈ O, c * o * c⁻¹ ∈ O := fun o ho =>
        (Subgroup.mem_normalizer_iff.mp (hYO hcY) o).mp ho
      have hO1 : d * u * w * c * (d * u * w)⁻¹ * c⁻¹ ∈ O := hyc
      have e : w * c * w⁻¹ * c⁻¹ =
          (u⁻¹ * (d⁻¹ * (d * u * w * c * (d * u * w)⁻¹ * c⁻¹) * d⁻¹⁻¹) * u) *
            (u⁻¹ * (c * u * c⁻¹)) := by
        have hdcomm : d * c = c * d := Subgroup.mem_centralizer_singleton_iff.mp hdc
        have hd' : d⁻¹ * c * d = c := by
          calc d⁻¹ * c * d = d⁻¹ * (c * d) := by group
            _ = d⁻¹ * (d * c) := by rw [hdcomm]
            _ = c := by group
        calc w * c * w⁻¹ * c⁻¹ = u⁻¹ * (u * w * c * w⁻¹ * u⁻¹) * u * c⁻¹ := by group
          _ = u⁻¹ * (u * w * c * w⁻¹ * u⁻¹ * (d⁻¹ * c * d)⁻¹) * u * (u⁻¹ * c * u * c⁻¹) := by
              rw [hd']; group
          _ = _ := by group
      rw [e]
      refine O.mul_mem ?_ (O.mul_mem (O.inv_mem huO) (hcO u huO))
      have h2 : d⁻¹ * (d * u * w * c * (d * u * w)⁻¹ * c⁻¹) * d⁻¹⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hYO (Y.inv_mem hdY)) _).mp hO1
      have h3 : u⁻¹ * (d⁻¹ * (d * u * w * c * (d * u * w)⁻¹ * c⁻¹) * d⁻¹⁻¹) * u⁻¹⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hYO (Y.inv_mem huY)) _).mp h2
      simpa using h3
    have h2 : w * c * w⁻¹ * c⁻¹ ∈ C3 := by
      have : w * c * w⁻¹ ∈ C3 :=
        (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
      exact C3.mul_mem this (C3.inv_mem (Subgroup.mem_zpowers c))
    have h3 : w * c * w⁻¹ * c⁻¹ = 1 := by
      set z := w * c * w⁻¹ * c⁻¹ with hz
      have hz3 : z ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
      have hord : orderOf (⟨z, h1⟩ : O) ∣ 3 :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hz3))
      have hord2 : orderOf (⟨z, h1⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      have h0 : orderOf (⟨z, h1⟩ : O) ∣ Nat.gcd 3 (Nat.card O) := Nat.dvd_gcd hord hord2
      rw [hO.gcd_eq_one] at h0
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h0))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : w * c * w⁻¹ = c := by
      have := congrArg (· * c) h3
      simpa using this
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c * w := by rw [this]
  refine ⟨d * u * d⁻¹, ⟨?_, Y.mul_mem (Y.mul_mem hdY huY) (Y.inv_mem hdY)⟩, d * w,
    ⟨Y.mul_mem hdY hwY, Subgroup.mul_mem _ hdc hwc⟩, by group⟩
  exact (Subgroup.mem_normalizer_iff.mp (hYO hdY) u).mp hu.1

end Res8

end CFSG.RankThree.PartTwo.Sec20
