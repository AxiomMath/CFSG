module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Str

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem pow_three_mem {d : G} (hd : d ∈ A6.o2Z L) : d ^ 3 ∈ pCoreOf 2 L := by
  obtain ⟨hdL, hdc⟩ := mem_o2Z_gc.1 hd
  have h3 : (⟨QuotientGroup.mk ⟨d, hdL⟩, hdc⟩ :
      ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) ^ 3 = 1 := by
    have := h.hhat.2.1
    rw [← this]
    exact pow_card_eq_one'
  have h4 : (QuotientGroup.mk (⟨d, hdL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    have := congrArg Subtype.val h3
    simpa using this
  have h5 : (⟨d, hdL⟩ : ↥L) ^ 3 ∈ CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h4
  exact coe_mem_pCoreOf_iff.2 h5

theorem mem_pCoreOf_of_two_power {d : G} (hd : d ∈ A6.o2Z L) {j : ℕ} (hj : d ^ 2 ^ j = 1) :
    d ∈ pCoreOf 2 L := by
  obtain ⟨hdL, -⟩ := mem_o2Z_gc.1 hd
  have h3 := h.pow_three_mem hd
  have h3' : (⟨d, hdL⟩ : ↥L) ^ 3 ∈ CFSG.pCore 2 ↥L := coe_mem_pCoreOf_iff.1 h3
  have hz3 : (QuotientGroup.mk (⟨d, hdL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h3'
  have hz2 : (QuotientGroup.mk (⟨d, hdL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ j = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (⟨d, hdL⟩ : ↥L) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hj)
    rw [this]
    exact Subgroup.one_mem _
  have hg := pow_gcd_eq_one.2 ⟨hz3, hz2⟩
  have hcop : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num)
  rw [hcop, pow_one] at hg
  exact coe_mem_pCoreOf_iff.2 ((QuotientGroup.eq_one_iff _).1 hg)

theorem three_dvd_card_o2Z : 3 ∣ Nat.card ↥(A6.o2Z L) := by
  have h1 := Subgroup.relIndex_mul_card (A6.o2Z L) L
  rw [inf_eq_left.2 (o2Z_le_gc L), h.relIndex_o2Z] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [card_of_hatA6 h.hhat] at h2
  exact ⟨Nat.card (CFSG.pCore 2 ↥L), by omega⟩

theorem exists_order_three : ∃ u ∈ A6.o2Z L, orderOf u = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h.three_dvd_card_o2Z
  exact ⟨(u : G), u.2, by rw [← hu]; exact Subgroup.orderOf_coe u⟩

theorem exists_zpow_mod {w u : G} (hw : w ∈ A6.o2Z L) (hwn : w ∉ pCoreOf 2 L)
    (hu : u ∈ A6.o2Z L) : ∃ k : ℤ, (w ^ k)⁻¹ * u ∈ pCoreOf 2 L := by
  obtain ⟨hwL, hwc⟩ := mem_o2Z_gc.1 hw
  obtain ⟨huL, huc⟩ := mem_o2Z_gc.1 hu
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L with hQ
  set z : Q := QuotientGroup.mk ⟨w, hwL⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hwn (coe_mem_pCoreOf_iff.2 ((QuotientGroup.eq_one_iff _).1 h1))
  have hcard : Nat.card (Subgroup.center Q) = 3 := h.hhat.2.1
  have hord : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := hcard ▸ Subgroup.orderOf_dvd_natCard _ hwc
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hz1
    · exact h1
  have hzp : Subgroup.zpowers z = Subgroup.center Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]
      exact hwc
    · rw [hcard, Nat.card_zpowers, hord]
  have hmem : (QuotientGroup.mk ⟨u, huL⟩ : Q) ∈ Subgroup.zpowers z := hzp ▸ huc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hmk : (QuotientGroup.mk ((⟨w, hwL⟩ : ↥L) ^ k) : Q) = QuotientGroup.mk ⟨u, huL⟩ := by
    rw [QuotientGroup.mk_zpow]
    exact hk
  have hq : ((⟨w, hwL⟩ : ↥L) ^ k)⁻¹ * ⟨u, huL⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.1 hmk
  exact ⟨k, coe_mem_pCoreOf_iff.2 hq⟩

theorem o2Z_le_of_mem {P : Subgroup G} (hOP : pCoreOf 2 L ≤ P) {d : G} (hdP : d ∈ P)
    (hd : d ∈ A6.o2Z L) (hdn : d ∉ pCoreOf 2 L) : A6.o2Z L ≤ P := by
  intro e he
  obtain ⟨k, hk⟩ := h.exists_zpow_mod hd hdn he
  have hee : e = d ^ k * ((d ^ k)⁻¹ * e) := by group
  rw [hee]
  exact P.mul_mem (P.zpow_mem hdP k) (hOP hk)

end H6Ctx

end CFSG.Quasithin.H13.U3.GC137
