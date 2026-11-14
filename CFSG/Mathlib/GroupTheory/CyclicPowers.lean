module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace IsCyclic

theorem exists_pow_eq_of_pow_card_div_eq_one {G : Type*} [Group G] [Finite G]
    [IsCyclic G] {n : ℕ} (hn : 0 < n) (hdiv : n ∣ Nat.card G) {u : G}
    (hu : u ^ (Nat.card G / n) = 1) : ∃ v : G, v ^ n = u := by
  classical
  obtain ⟨g, hg⟩ := exists_zpow_surjective G
  haveI : Fintype G := Fintype.ofFinite G
  have hgen : ∀ x : G, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨k, hk⟩ := hg x
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
  have htop : Subgroup.zpowers g = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
  have hord : orderOf g = Nat.card G := by
    rw [← Fintype.card_zpowers (x := g), ← Nat.card_eq_fintype_card,
      htop, Subgroup.card_top]
  have hmem := hgen u
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have hcard : 0 < Nat.card G := Nat.card_pos
  have hpos : 0 < Nat.card G / n := Nat.div_pos (Nat.le_of_dvd hcard hdiv) hn
  have hmul : n * (Nat.card G / n) = Nat.card G := by
    have h := Nat.mod_add_div (Nat.card G) n
    rw [Nat.mod_eq_zero_of_dvd hdiv, zero_add] at h
    exact h
  have hp : g ^ (i * (Nat.card G / n)) = 1 := by
    rw [pow_mul, hi]
    exact hu
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hord] at hd
  have hd' : n * (Nat.card G / n) ∣ i * (Nat.card G / n) := by rwa [hmul]
  have hni : n ∣ i := (Nat.mul_dvd_mul_iff_right hpos).mp hd'
  obtain ⟨k, hk⟩ := hni
  refine ⟨g ^ k, ?_⟩
  calc (g ^ k) ^ n = g ^ (k * n) := (pow_mul g k n).symm
    _ = g ^ i := by rw [mul_comm, ← hk]
    _ = u := hi

end IsCyclic
