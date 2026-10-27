module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.OrderThreeLift
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.Sylow3

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace Stellmacher.L3YC

section Fiber

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_same_image {L : Subgroup G} (hq : IsLnTwoQuot L 3) {F : Type} [Field F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α) {y x x' : G} (hx : x ∈ L) (hx' : x' ∈ L)
    (hx3 : orderOf x = 3) (hx'3 : orderOf x' = 3) (hxy : y * x = x * y) (hx'y : y * x' = x' * y)
    (hxb : orderOf (α ⟨x, hx⟩) = 3) (hαx : α ⟨x', hx'⟩ = α ⟨x, hx⟩) :
    ∃ o ∈ pCoreOf 2 L, y * o = o * y ∧ x' = o * x * o⁻¹ := by
  classical
  set xb : ↥(StatedSL 3 F) := α ⟨x, hx⟩ with hxbdef
  let K : Subgroup G := Subgroup.map L.subtype
    ((Subgroup.zpowers xb).comap α ⊓ (Subgroup.centralizer ({y} : Set G)).subgroupOf L)
  have hmemK : ∀ l : G, l ∈ K ↔ ∃ hl : l ∈ L, α ⟨l, hl⟩ ∈ Subgroup.zpowers xb ∧ y * l = l * y := by
    intro l
    constructor
    · rintro ⟨l', ⟨h1, h2⟩, rfl⟩
      refine ⟨l'.2, ?_, ?_⟩
      · exact h1
      · exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp h2)).symm
    · rintro ⟨hl, h1, h2⟩
      exact ⟨⟨l, hl⟩, ⟨h1, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h2.symm)⟩, rfl⟩
  have hxK : x ∈ K := (hmemK x).mpr ⟨hx, Subgroup.mem_zpowers xb, hxy⟩
  have hx'K : x' ∈ K := (hmemK x').mpr ⟨hx', by rw [hαx]; exact Subgroup.mem_zpowers xb, hx'y⟩
  have hKval : padicValNat 3 (Nat.card K) = 1 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨j, hj⟩ := card_eq_of_isLnTwoQuot hq
    have hKL : K ≤ L := Subgroup.map_subtype_le _
    have hdvd : Nat.card K ∣ 168 * 2 ^ j := hj ▸ Subgroup.card_dvd_of_le hKL
    have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have h3 : 3 ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨x, hxK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, hx3] at this
    have h9 : ¬ 9 ∣ Nat.card K := by
      intro h
      have h' : 9 ∣ 168 * 2 ^ j := h.trans hdvd
      have hcop : Nat.Coprime 9 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
      have := hcop.dvd_of_dvd_mul_right h'
      omega
    have e1 := (padicValNat_dvd_iff_le (p := 3) hKpos (n := 1)).mp (by simpa using h3)
    have e2 : ¬ 2 ≤ padicValNat 3 (Nat.card K) := fun h =>
      h9 (by simpa using (padicValNat_dvd_iff_le (p := 3) hKpos (n := 2)).mpr h)
    omega
  obtain ⟨k, hkK, hk⟩ := exists_conj_order_three hKval hx'K hxK hx'3 hx3
  obtain ⟨hkL, hkα, hky⟩ := (hmemK k).mp hkK
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkα
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
  set X : ↥L := ⟨x, hx⟩ with hX
  set X' : ↥L := ⟨x', hx'⟩ with hX'
  set k' : ↥L := ⟨k, hkL⟩ with hk'
  have hX3 : orderOf X = 3 := by rw [hX, Subgroup.orderOf_mk]; exact hx3
  have hkx : k' * X' * k'⁻¹ = X ^ m := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Subgroup.coe_zpow]
    exact hm.symm
  have hxbm : xb ^ m = xb := by
    have h1 := congrArg α hkx
    rw [map_mul, map_mul, map_inv, map_zpow, hαx, ← hj] at h1
    rw [← h1]
    have hc : Commute (xb ^ j) xb := (Commute.refl xb).zpow_left j
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hXm : X ^ m = X := by
    have h1 : xb ^ (m - 1) = 1 := by
      rw [zpow_sub, zpow_one, hxbm, mul_inv_cancel]
    have h2 : (3 : ℤ) ∣ m - 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := xb) (i := m - 1)).mpr h1
      rwa [hxb] at this
    have h3 : X ^ (m - 1) = 1 := by
      apply (orderOf_dvd_iff_zpow_eq_one (x := X) (i := m - 1)).mp
      rwa [hX3]
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h3
    exact h3
  have hkx' : k * x' * k⁻¹ = x := by
    have := congrArg Subtype.val (hkx.trans hXm)
    simpa using this
  have hxj : x ^ (-j) ∈ L := Subgroup.zpow_mem _ hx _
  have ho₀L : k * x ^ (-j) ∈ L := L.mul_mem hkL hxj
  have ho₀α : α ⟨k * x ^ (-j), ho₀L⟩ = 1 := by
    have : (⟨k * x ^ (-j), ho₀L⟩ : ↥L) = k' * X ^ (-j) := rfl
    rw [this, map_mul, map_zpow, ← hj, ← hxbdef, ← zpow_add, add_neg_cancel, zpow_zero]
  have ho₀P : k * x ^ (-j) ∈ pCoreOf 2 L := by
    refine Subgroup.mem_map.mpr ⟨⟨k * x ^ (-j), ho₀L⟩, ?_, rfl⟩
    have : (⟨k * x ^ (-j), ho₀L⟩ : ↥L) ∈ α.ker := ho₀α
    rw [hα.2] at this
    exact this
  have hoP : x ^ (-j) * (k * x ^ (-j))⁻¹ * (x ^ (-j))⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hxj) _).mp
      ((pCoreOf 2 L).inv_mem ho₀P)
  refine ⟨x ^ (-j) * (k * x ^ (-j))⁻¹ * (x ^ (-j))⁻¹, hoP, ?_, ?_⟩
  · have hyx : Commute y x := hxy
    have hyk : Commute y k := hky
    have hy1 : Commute y (x ^ (-j)) := hyx.zpow_right _
    exact ((hy1.mul_right (hyk.mul_right hy1).inv_right).mul_right hy1.inv_right).eq
  · have : x' = k⁻¹ * x * k := by
      rw [← hkx']; group
    rw [this]
    group

end Fiber

end Stellmacher.L3YC

end CFSG.Quasithin
