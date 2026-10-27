module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem eq_of_normal_of_not_le_centralizer [Finite G] {D N M : Subgroup G} (hND : N ≤ D)
    (hMD : M ≤ D) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hDM : D ≤ Subgroup.normalizer (M : Set G)) (hN : IsSimpleGroup N)
    (hcard : Nat.card N = Nat.card M) (hc : ¬ N ≤ Subgroup.centralizer (M : Set G)) : N = M := by
  have hnorm : ((N ⊓ M).subgroupOf N).Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxN, hxM⟩
      exact ⟨N.mul_mem (N.mul_mem hn hxN) (N.inv_mem hn),
        (Subgroup.mem_normalizer_iff.mp (hDM (hND hn)) x).mp hxM⟩
    · rintro ⟨hxN, hxM⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hDM (hND hn)) x).mpr hxM⟩
      have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
      rw [this]
      exact N.mul_mem (N.mul_mem (N.inv_mem hn) hxN) hn
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ M).subgroupOf N) with hbot | htop
  · exfalso
    apply hc
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 : n * m * n⁻¹ * m⁻¹ ∈ N ⊓ M := by
      refine ⟨?_, M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDM (hND hn)) m).mp hm)
        (M.inv_mem hm)⟩
      have : n * m * n⁻¹ * m⁻¹ = n * (m * n⁻¹ * m⁻¹) := by group
      rw [this]
      exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp (hDN (hMD hm)) n⁻¹).mp (N.inv_mem hn))
    have h2 : (⟨n * m * n⁻¹ * m⁻¹, h1.1⟩ : ↥N) ∈ (N ⊓ M).subgroupOf N :=
      Subgroup.mem_subgroupOf.mpr h1
    rw [hbot, Subgroup.mem_bot] at h2
    have h3 : n * m * n⁻¹ * m⁻¹ = 1 := congrArg Subtype.val h2
    calc m * n = (n * m * n⁻¹ * m⁻¹)⁻¹ * (n * m) := by group
      _ = n * m := by rw [h3, inv_one, one_mul]
  · have hle : N ≤ M := fun n hn => by
      have h : (⟨n, hn⟩ : ↥N) ∈ (N ⊓ M).subgroupOf N := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h).2
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

theorem mem_of_mem_sup_zpowers [Finite G] {R : Subgroup G} {b c t : G}
    (hRb : R ≤ Subgroup.centralizer ({b} : Set G)) (hR3 : ¬ 3 ∣ Nat.card R) (hb : orderOf b = 3)
    (hc : c ∈ R ⊔ Subgroup.zpowers b) (htc : t * c = c * t) (htb : t * b * t⁻¹ = b⁻¹) :
    c ∈ R := by
  have hbR : Subgroup.zpowers b ≤ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : b * x * b⁻¹ = x := by
        rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hRb hx))]
        group
      rwa [this]
    · intro hx
      have : b * x * b⁻¹ = x := by
        have hx' : b * x * b⁻¹ ∈ R := hx
        have h := Subgroup.mem_centralizer_singleton_iff.mp (hRb hx')
        calc b * x * b⁻¹ = b⁻¹ * (b * (b * x * b⁻¹)) * b⁻¹ * b := by group
          _ = b⁻¹ * ((b * x * b⁻¹) * b) * b⁻¹ * b := by rw [h]
          _ = x := by group
      rwa [this] at hx
  have hc' : c ∈ ((R ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := hc
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ hbR] at hc'
  obtain ⟨r, hr, _, ⟨i, rfl⟩, rfl⟩ := hc'
  set m := Nat.card R with hm
  have hrb : Commute r ((fun j : ℤ => b ^ j) i) := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hRb hr)
    exact (Commute.zpow_right (show Commute r b from h) i)
  have hrm : r ^ m = 1 := by
    have h := pow_card_eq_one' (G := ↥R) (x := ⟨r, hr⟩)
    exact congrArg Subtype.val h
  have hcm : (r * b ^ i) ^ m = b ^ (i * m) := by
    simp only at hrb
    rw [hrb.mul_pow, hrm, one_mul, zpow_mul, zpow_natCast]
  have htcm : t * (r * b ^ i) ^ m * t⁻¹ = (r * b ^ i) ^ m := by
    have h : Commute t ((fun j : ℤ => r * b ^ j) i) := htc
    rw [(h.pow_right m).eq, mul_inv_cancel_right]
  rw [hcm] at htcm
  have htbz : t * b ^ (i * m) * t⁻¹ = b⁻¹ ^ (i * m) := by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htb]
  rw [htbz, inv_zpow'] at htcm
  have h2 : b ^ (2 * (i * m)) = 1 := by
    rw [two_mul, zpow_add]
    nth_rewrite 2 [← htcm]
    rw [← zpow_add, add_neg_cancel, zpow_zero]
  have h3 : (3 : ℤ) ∣ 2 * (i * m) := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hb] at h
    exact_mod_cast h
  have hi : (3 : ℤ) ∣ i := by
    rcases Int.prime_three.dvd_or_dvd h3 with h | h
    · exact absurd h (by decide)
    · rcases Int.prime_three.dvd_or_dvd h with h | h
      · exact h
      · exact absurd (Int.natCast_dvd_natCast.mp h) hR3
  have hbi : b ^ i = 1 := by
    refine orderOf_dvd_iff_zpow_eq_one.mp ?_
    rw [hb]
    exact_mod_cast hi
  show r * b ^ i ∈ R
  rw [hbi, mul_one]
  exact hr

end CFSG.GroupTheory
