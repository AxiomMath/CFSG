module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools
import CFSG.RankThree.PartTwo.Late.Uniqueness
import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint

namespace Res417Three

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_center_of_pow_two (h2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G}
    (hL : L.IsSubnormal) {w : L} (hw : w ∈ Subgroup.center L) {k : ℕ} (hwk : w ^ (2 ^ k) = 1) :
    w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hw j) g), mul_inv_cancel_right]
    exact hx
  have hp2 : IsPGroup 2 (Subgroup.zpowers w) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle1 : Subgroup.zpowers w ≤ CFSG.Open.pCore 2 L := by
    exact le_sSup ⟨hnorm, hp2⟩
  have hle2 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hL
  rw [h2] at hle2
  have hmem : (w : G) ∈ (⊥ : Subgroup G) :=
    hle2 ((Subgroup.map_mono (f := L.subtype) hle1) ⟨w, Subgroup.mem_zpowers w, rfl⟩)
  rw [Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Res417Three

open Res417Three

section Certs


variable {G : Type} [Group G] [Finite G] {L A E : Subgroup G} {c : G} {m : ℕ}

theorem IsInnerInConf417.mem_centralizer (h : IsInnerInConf417 L A E c m) :
    c ∈ Subgroup.centralizer (L : Set G) := by
  have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
    h.2.2.2.2.1.2.2.1 ▸ Subgroup.mem_zpowers c
  exact this.2

theorem IsInnerInConf417.mem_A (h : IsInnerInConf417 L A E c m) : c ∈ A := by
  have : c ∈ A ⊓ Subgroup.centralizer (L : Set G) :=
    h.2.2.2.2.1.2.2.1 ▸ Subgroup.mem_zpowers c
  exact this.1

theorem IsInnerInConf417.mem_center (h : IsInnerInConf417 L A E c m) :
    (⟨c, h.2.2.2.2.2.2.2.2.2⟩ : L) ∈ Subgroup.center L :=
  Subgroup.mem_center_iff.mpr fun y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp h.mem_centralizer y y.2)

theorem IsInnerInConf417.three_dvd_card_center (h : IsInnerInConf417 L A E c m) :
    3 ∣ Nat.card (Subgroup.center L) := by
  have hord : orderOf (⟨⟨c, h.2.2.2.2.2.2.2.2.2⟩, h.mem_center⟩ : Subgroup.center L) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, h.2.2.2.2.1.2.2.2.1]
  exact hord ▸ orderOf_dvd_natCard _

theorem IsInnerInConf417.isPGroup_center (h : IsInnerInConf417 L A E c m)
    (hZ : ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ Nat.card (Subgroup.center L)) :
    IsPGroup 3 (Subgroup.center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center L) := by
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hz2 : (z : L) ^ (2 ^ 1) = 1 := by
      rw [pow_one, ← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
    have h1 := eq_one_of_mem_center_of_pow_two h.2.1 h.2.2.1.2 z.2 hz2
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    omega
  refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.card_pos (α := Subgroup.center L)).ne' fun {q} hq hqd => ?_)
  have hq2 := hq.two_le
  rcases (show q = 2 ∨ q = 3 ∨ 3 < q by omega) with rfl | rfl | h3
  · exact absurd hqd h2
  · rfl
  · exact absurd hqd (hZ q hq h3)

theorem IsInnerInConf417.card_center_eq_three (h : IsInnerInConf417 L A E c m)
    (hdvd : Nat.card (Subgroup.center L) ∣ 3) : Nat.card (Subgroup.center L) = 3 :=
  Nat.dvd_antisymm hdvd h.three_dvd_card_center

theorem IsInnerInConf417.mem_zpowers_of_mem_center (h : IsInnerInConf417 L A E c m) {z : L}
    (hz : z ∈ Subgroup.center L) (hz3 : z ^ 3 = 1) : (z : G) ∈ Subgroup.zpowers c := by
  obtain ⟨hAmax, -, hAc, -⟩ := h.2.2.2.2.1
  have hcomm : ∀ a ∈ A, a * (z : G) = (z : G) * a := by
    intro a ha
    obtain ⟨l, hl, hconj⟩ := h.inner a ha
    have h2 : l * (z : G) = (z : G) * l :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    have h3 : a * (z : G) * a⁻¹ = z := by rw [hconj z z.2, h2, mul_inv_cancel_right]
    calc a * (z : G) = a * (z : G) * a⁻¹ * a := by group
      _ = (z : G) * a := by rw [h3]
  have hz3' : (z : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hz3
    simpa using this
  have hab := Sec15.isElemAbelian_sup_zpowers hAmax.prop hz3' hcomm
  have hle := hAmax.2 hab le_sup_left
  have hzA : (z : G) ∈ A := hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hzC : (z : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  rw [← hAc]
  exact ⟨hzA, hzC⟩

theorem IsInnerInConf417.card_center_dvd_three_of_exponent (h : IsInnerInConf417 L A E c m)
    (hZ : ∀ z ∈ Subgroup.center L, z ^ 3 = 1) : Nat.card (Subgroup.center L) ∣ 3 := by
  have hle : (Subgroup.center L).map L.subtype ≤ Subgroup.zpowers c := by
    rintro _ ⟨z, hz, rfl⟩
    exact h.mem_zpowers_of_mem_center hz (hZ z hz)
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective L.subtype_injective, Nat.card_zpowers,
    h.2.2.2.2.1.2.2.2.1] at h1

end Certs

end CFSG.RankThree.PartTwo.Sec4
