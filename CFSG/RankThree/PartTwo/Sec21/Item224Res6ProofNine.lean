module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

theorem eq_of_card_nine {G : Type*} [Group G] {E H : Subgroup G} (hE9 : Nat.card E = 9)
    (hHE : H ≤ E) {a b : G} (ha : a ∈ H) (ha3 : orderOf a = 3) (hb : b ∈ H)
    (hba : b ∉ Subgroup.zpowers a) : H = E := by
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  have hHdvd : Nat.card H ∣ 9 := hE9 ▸ Subgroup.card_dvd_of_le hHE
  have hHfin : Finite H := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0] at hHdvd
    norm_num at hHdvd
  have haH : Subgroup.zpowers a ≤ H := Subgroup.zpowers_le.mpr ha
  have h3 : 3 ∣ Nat.card H := by
    rw [← ha3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le haH
  have hne : Nat.card H ≠ 3 := by
    intro h3'
    apply hba
    have : Subgroup.zpowers a = H :=
      Subgroup.eq_of_le_of_card_ge haH (by rw [h3', Nat.card_zpowers, ha3])
    rw [this]
    exact hb
  have h9 : Nat.card H = 9 := by
    obtain ⟨i, hi, hHi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card H ∣ 3 ^ 2 by simpa using hHdvd)
    interval_cases i
    · rw [hHi] at h3
      norm_num at h3
    · exact absurd (by simpa using hHi) hne
    · rw [hHi]
      norm_num
  exact Subgroup.eq_of_le_of_card_ge hHE (by rw [hE9, h9])

theorem not_mem_zpowers_mul {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha3 : orderOf a = 3) (hb3 : b ^ 3 = 1) (hba : b ∉ Subgroup.zpowers a) :
    a ∉ Subgroup.zpowers (a * b) := by
  intro hmem
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcomm : Commute a b := hab
  rw [hcomm.mul_zpow] at hi
  have hbi : b ^ i = a ^ (1 - i) := by
    rw [zpow_sub, zpow_one]
    calc b ^ i = (a ^ i)⁻¹ * (a ^ i * b ^ i) := by group
      _ = (a ^ i)⁻¹ * a := by rw [hi]
      _ = a * (a ^ i)⁻¹ := ((Commute.zpow_left (Commute.refl a) i).inv_left).eq
  have hb1 : b ≠ 1 := fun h1 => hba (h1 ▸ one_mem _)
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  by_cases hbi1 : b ^ i = 1
  · have h1 : ((orderOf b : ℕ) : ℤ) ∣ i := orderOf_dvd_iff_zpow_eq_one.mpr hbi1
    have h2 : a ^ (1 - i) = 1 := hbi ▸ hbi1
    have h3 : ((orderOf a : ℕ) : ℤ) ∣ 1 - i := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hbord] at h1
    rw [ha3] at h3
    have h4 := dvd_add h1 h3
    rw [add_sub_cancel] at h4
    norm_num at h4
  · apply hba
    have hbi3' : (b ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
    have hbi3 : orderOf (b ^ i) = 3 := orderOf_eq_prime hbi3' hbi1
    have hfin : Finite (Subgroup.zpowers b) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hbord]; norm_num)
    have hle : Subgroup.zpowers (b ^ i) ≤ Subgroup.zpowers b :=
      Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers b i)
    have heq : Subgroup.zpowers (b ^ i) = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hbi3, hbord])
    have hbmem : b ∈ Subgroup.zpowers (b ^ i) := heq ▸ Subgroup.mem_zpowers b
    have hle' : Subgroup.zpowers (b ^ i) ≤ Subgroup.zpowers a :=
      Subgroup.zpowers_le.mpr (hbi ▸ Subgroup.zpow_mem_zpowers a (1 - i))
    exact hle' hbmem

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
